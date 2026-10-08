package hugin.runtime

import hugin.util.*
import hugin.compiler.*
import hugin.ir.*
import hugin.obj.RelKind
import hugin.obj.typing.TypeOps

/** Evaluates a compiled program: loads input facts, runs the engine, renders output relations and query
 *  answers (Section 9.6). The compilation result is not modified; input diagnostics are returned. */
object Evaluation:
  /** The answers of one query: the query as written and its answer lines (`yes.`, `no.` or bindings). */
  final case class Answers(query: String, lines: List[String])

  /** `facts` are the printed facts of the shown relations; `answers` follow the queries in program order. */
  final case class Result(facts: List[String], answers: List[Answers], stats: List[ComponentStats]):
    /** The output of Section 9.6: the facts, then each query followed by its answers. */
    def output: List[String] = facts ++ answers.flatMap(a => a.query :: a.lines)

    /** One line per component that ran at least one round, for `--stats`. */
    def statistics: List[String] =
      for s <- stats if s.rounds > 0
      yield s"(* {${s.rels.mkString(", ")}}: ${s.rounds} round(s) *)"

  /** `result` is empty if the program could not be evaluated (compile errors or invalid input facts). */
  final case class Outcome(result: Option[Result], diagnostics: List[Diagnostic])

  def run(c: Context, factFiles: List[SourceFile], allRelations: Boolean = false): Outcome =
    val core = c.unit.core
    if core == null || c.reporter.hasErrors then return Outcome(None, Nil)
    val prog = core.nn
    val engine = Engine(prog)
    val reporter = Reporter()
    val loader = FactLoader(engine, prog, TypeOps(c.unit.prog.nn), reporter)
    factFiles.foreach(loader.load)
    if reporter.hasErrors then return Outcome(None, reporter.sorted)
    engine.run()
    def directives(r: hugin.obj.RelSym) = prog.directives(prog.tag(r))
    val explicit = prog.rels.filter(directives(_).output)
    val shown =
      if allRelations then prog.rels.filterNot(_.isData) // data constructors' values are not facts of a relation
      else if explicit.nonEmpty then explicit
      else if prog.queries.nonEmpty then Vector.empty
      else prog.rels.filter(r => r.kind == RelKind.Plain && !directives(r).input)
    val answers = prog.queries.toList.map { q =>
      val text = if q.source.span.exists then q.source.span.text.replaceAll("\\s+", " ") else hugin.obj.ObjPrinter.query(q.source)
      val as = engine.answers(q)
      val lines =
        if q.vars.isEmpty then List(if as.nonEmpty then "yes." else "no.")
        else if as.isEmpty then List("no.")
        else as.map(a => q.vars.zip(a).map((v, w) => s"$v = ${engine.show(w)}").mkString(", ") + ".").sorted.toList
      Answers(text, lines)
    }
    val facts = shown.flatMap(r => engine.facts(prog.tag(r))).sorted.toList
    Outcome(Some(Result(facts, answers, engine.stats.toList)), reporter.sorted)
