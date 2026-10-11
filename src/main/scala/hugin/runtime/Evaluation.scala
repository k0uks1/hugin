package hugin.runtime

import hugin.util.*
import hugin.compiler.*
import hugin.ir.*
import hugin.obj.{ObjProgram, RelKind}
import hugin.obj.typing.TypeOps
import scala.collection.mutable

/** Evaluates a compiled program: loads input facts, runs the engine, renders output relations and query
 *  answers (Section 9.6). The compilation result is not modified; input diagnostics are returned. */
object Evaluation:
  /** The answers of one query: the query as written, its variables and one row of values per answer
   *  (printed as in input facts), in the order of their lines. */
  final case class Answers(query: String, vars: List[String], rows: List[List[String]]):
    /** The answer lines: `yes.` or `no.` for a query without variables, else `no.` or one line of
     *  bindings per row (`X = a, Y = b.`). */
    def lines: List[String] =
      if vars.isEmpty then List(if rows.nonEmpty then "yes." else "no.")
      else if rows.isEmpty then List("no.")
      else rows.map(Answers.line(vars, _))

  object Answers:
    def line(vars: List[String], row: List[String]): String = vars.zip(row).map((v, w) => s"$v = $w").mkString(", ") + "."

  /** The facts of a shown relation: one row of arguments (printed as in input facts) per fact, sorted as
   *  the printed facts. */
  final case class Relation(name: String, rows: List[List[String]])

  /** `facts` are the printed facts of the shown relations (and `relations` the same facts as rows);
   *  `answers` follow the queries in program order. */
  final case class Result(facts: List[String], answers: List[Answers], stats: List[ComponentStats], relations: List[Relation] = Nil):
    /** The output of Section 9.6: the facts, then each query followed by its answers. */
    def output: List[String] = facts ++ answers.flatMap(a => a.query :: a.lines)

    /** One line per component that ran at least one round, for `--stats`. */
    def statistics: List[String] =
      for s <- stats if s.rounds > 0
      yield s"(* {${s.rels.mkString(", ")}}: ${s.rounds} round(s) *)"

  /** `result` is empty if the program could not be evaluated (compile errors or invalid input facts). */
  final case class Outcome(result: Option[Result], diagnostics: List[Diagnostic])

  /** The items of a facts file (with its text) with the syntax errors found while parsing it
   *  ([[FactLoader.parse]]). */
  final class ParsedFacts(val items: List[hugin.syntax.Trees.Item], val diagnostics: List[Diagnostic], val text: String):
    /** The names the facts mention (identifiers and paths; [[ComponentKeys.facts]]), computed when an
     *  evaluation is reused. */
    lazy val names: Set[String] =
      val out = mutable.HashSet.empty[String]
      def visit(t: hugin.syntax.Tree): Unit = t match
        case hugin.syntax.Trees.Ident(n) => out += n
        case hugin.syntax.Trees.Apply(f, a) => visit(f); visit(a)
        case hugin.syntax.Trees.Parens(i) => visit(i)
        case _: hugin.syntax.Trees.Lit | _: hugin.syntax.Trees.VarRef | _: hugin.syntax.Trees.Wildcard =>
        case other => out ++= hugin.core.elab.ElabOrder.mentions(hugin.syntax.Trees.Query(other)(other.span))
      items.foreach {
        case hugin.syntax.Trees.Rule(None, heads, None) => heads.foreach(visit)
        case other => out ++= hugin.core.elab.ElabOrder.mentions(other)
      }
      out.toSet

  def parseFacts(src: SourceFile): ParsedFacts =
    val reporter = Reporter()
    ParsedFacts(FactLoader.parse(src, reporter), reporter.diagnostics, src.content)

  /** An evaluated program: the engine after loading the facts files and running the rules of `prog` to
   *  their fixpoint (`evaluated`), or, if the facts were invalid, after loading them (not `evaluated`).
   *  Answering queries and printing relations ([[render]]) only read it; a later evaluation may copy
   *  relations from it (`trace`, [[Reuse]]). */
  final class Fixpoint(
      val prog: CoreProgram,
      val obj: ObjProgram,
      val engine: Engine,
      val evaluated: Boolean,
      val diagnostics: List[Diagnostic],
      val trace: Option[Reuse.Trace] = None
  )

  /** Loads `facts` (with `ops`, the subtyping of the object program `obj`, for their types) and evaluates
   *  `prog`, copying from `previous`, an earlier evaluation, what it would compute again ([[Reuse]]). */
  def fixpoint(prog: CoreProgram, obj: ObjProgram, ops: TypeOps, facts: List[ParsedFacts], previous: Option[Fixpoint] = None): Fixpoint =
    val keys = ComponentKeys(prog, obj)
    val earlier = previous.filter(_.evaluated).flatMap(p => p.trace.map(Reuse.Earlier(p.prog, p.obj, p.engine, _)))
    lazy val reused = Engine(prog)
    earlier.flatMap(e => Reuse.restore(reused, prog, keys, facts, e)) match
      case Some((steps, sizes)) => evaluate(prog, reused, keys, facts, steps, sizes, previous.get.diagnostics, obj)
      case None =>
        val engine = Engine(prog)
        val reporter = Reporter()
        val loader = FactLoader(engine, prog, ops, reporter)
        for f <- facts do
          f.diagnostics.foreach(reporter.report)
          loader.load(f.items)
        if reporter.hasErrors then Fixpoint(prog, obj, engine, false, reporter.sorted)
        else
          val loaded = prog.rels.indices.filter(engine.store(_).size > 0).map(t => t -> engine.store(t).size).toMap
          evaluate(prog, engine, keys, facts, 0, Vector(loaded), reporter.sorted, obj)

  /** Evaluates the components of `prog` from the `steps`-th on, recording the sizes after each. */
  private def evaluate(
      prog: CoreProgram,
      engine: Engine,
      keys: ComponentKeys,
      facts: List[ParsedFacts],
      steps: Int,
      sizes: Vector[Map[Int, Int]],
      diagnostics: List[Diagnostic],
      obj: ObjProgram
  ): Fixpoint =
    val trace = mutable.ArrayBuffer.from(sizes)
    def writes(ci: Int) = Reuse.writes(prog, ci, keys.rules(ci))
    engine.run(steps until prog.components.length, step = ci => trace += writes(ci).map(t => t -> engine.store(t).size).toMap)
    Fixpoint(prog, obj, engine, true, diagnostics, Some(Reuse.Trace(facts, trace.toVector)))

  def run(c: Context, factFiles: List[SourceFile], allRelations: Boolean = false): Outcome =
    val core = c.unit.core
    if core == null || c.reporter.hasErrors then return Outcome(None, Nil)
    val prog = core.nn
    render(prog, fixpoint(prog, c.unit.prog.nn, TypeOps(c.unit.prog.nn), factFiles.map(parseFacts)), allRelations)

  /** The output relations and query answers of `prog` over a fixpoint of its rules. The fixpoint may have
   *  been computed for another program whose relations and lowered rules are equal ([[LoweredRules]],
   *  `hugin.query.Fixpoint`), so that the queries of `prog` refer to the same relation tags. */
  def render(prog: CoreProgram, fixpoint: Fixpoint, allRelations: Boolean): Outcome =
    if !fixpoint.evaluated then return Outcome(None, fixpoint.diagnostics)
    val engine = fixpoint.engine
    def directives(r: hugin.obj.RelSym) = prog.directives(prog.tag(r))
    val explicit = prog.rels.filter(directives(_).output)
    val shown =
      if allRelations then prog.rels.filter(_.kind != RelKind.Proof)
      else if explicit.nonEmpty then explicit
      else if prog.queries.nonEmpty then Vector.empty
      else prog.rels.filter(r => r.kind == RelKind.Plain && !directives(r).input)
    val answers = prog.queries.toList.map { q =>
      val text = if q.source.span.exists then q.source.span.text.replaceAll("\\s+", " ") else hugin.obj.ObjPrinter.query(q.source)
      val vars = q.vars.toList
      val rows = engine.answers(q).map(_.toList.map(engine.show(_)))
      Answers(text, vars, if vars.isEmpty then rows else rows.sortBy(Answers.line(vars, _)))
    }
    val facts = shown.flatMap(r => engine.facts(prog.tag(r))).sorted.toList
    val relations = shown.toList.map { r =>
      val (name, rows) = engine.rows(prog.tag(r))
      Relation(name, rows.sortBy(row => (name :: row).mkString(" ") + "."))
    }
    Outcome(Some(Result(facts, answers, engine.stats.toList, relations)), fixpoint.diagnostics)
