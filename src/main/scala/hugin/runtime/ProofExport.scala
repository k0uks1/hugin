package hugin.runtime

import hugin.compiler.CompilationUnit
import hugin.ir.{CoreProgram, Id}
import hugin.obj.*
import hugin.obj.transform.ProofRule
import hugin.util.diagnostics.Json
import scala.collection.mutable

/** `--export-proofs`: the derivations of a run as a proof certificate in the JSON format of Tantow,
 *  Gerlach, Mennicke and Krötzsch, "Verifying Datalog Reasoning with Lean" (ITP 2025; the checker
 *  `knowsys/CertifyingDatalog`, v0.2.0), whose Lean checker validates it (reference: object/io, "Proof
 *  export").
 *
 *  The certificate has the exported rules (`program`), and a proof tree (`trees`) or an ordered proof
 *  graph (`graph`) for every fact of every relation of those rules. A value is the constant written as
 *  `hugin run` prints it; a relation is named by its qualified name. A negated atom `not r t̄` is the atom
 *  `"not r"(t̄)` and a comparison `l op r` the atom `"op"(l, r)`: atoms of *assumption relations*, which
 *  the proofs have as leaves, so that the checker validates the positive structure and a reader checks the
 *  assumptions against the run (a negated atom holds if no fact of the run matches it). A local variable
 *  of a negated atom is the constant of its name (`_` for a wildcard), which no value prints as.
 *
 *  Rules outside the exported fragment ([[hugin.obj.transform.ProofFragment]]) are left out with a
 *  warning. A fact without a derivation by the exported rules is a leaf: a fact of an input relation is
 *  also a rule without body (as in Tantow et al.'s examples); any other such fact is an *assumed fact*,
 *  listed under `hugin`. The facts a fact is proved from are chosen by a breadth-first fixpoint over the
 *  recorded rule instances, so every proof is well founded and of least depth. */
object ProofExport:
  enum Format(val name: String):
    case Trees extends Format("trees")
    case OrderedGraph extends Format("ordered-graph")

  object Format:
    def parse(s: String): Option[Format] = Format.values.find(_.name == s)

  /** The certificate and the warnings to print. */
  final case class Export(json: Json, warnings: List[String])

  /** The version of the `hugin` member of the certificate. */
  val Version = 1

  private[runtime] final case class Atom(symbol: String, terms: List[String])

  /** A child in a proof: a fact of the run, or an atom of an assumption relation. */
  private[runtime] enum Node:
    case Fact(id: Id)
    case Leaf(atom: Atom)

  /** One recorded rule instance: the derived fact and the children in the order of the rule's body. */
  private[runtime] final class Instance(val head: Id, val children: Vector[Node]):
    val facts: Vector[Id] = children.collect { case Node.Fact(id) => id }.distinct

  /** The derivations of a run: for every fact of the exported relations and every fact a proof uses, the
   *  instance it is proved by (`None`: a leaf), in the order the facts were settled, in which every fact
   *  comes after the facts its proof uses. */
  private[runtime] final class Derivations(
      val roots: Vector[Id],
      val proof: collection.Map[Id, Option[Instance]],
      val order: Vector[Id],
      val rules: Vector[ExportedRule]
  )

  private def constant(engine: Engine, t: Term, env: Map[String, Any]): String = t match
    case Term.Var(n) => env.get(n).fold(Var.display(n))(engine.show(_))
    case Term.App(c, Nil) => c.sym.displayName
    case other => engine.value(other, env).fold(ObjPrinter.term(other))(engine.show(_))

  /** The derivations of the exported rules of a run (shared with `--certify`, [[Certify]]). */
  private[runtime] def derivations(unit: CompilationUnit, prog: CoreProgram, engine: Engine): Derivations =
    def constant(t: Term, env: Map[String, Any]): String = ProofExport.constant(engine, t, env)

    // the recorded instances of the exported rules
    val instances = mutable.ArrayBuffer.empty[Instance]
    for pr <- unit.proofRules do
      val rel = engine.store(prog.tag(pr.rel))
      for n <- rel.tuples.indices do
        val t = rel.tuples(n)
        var i = 1
        var current = true
        val children = pr.rel.premises.map { p =>
          val ws = t.slice(i, i + p.width)
          i += p.width
          p match
            case Premise.Pos(_) =>
              val id = ws(0).asInstanceOf[Id]
              // a premise of a bound relation may have been replaced by a better tuple since
              current &&= engine.store(id.rel).current(id.n)
              Node.Fact(id)
            case Premise.Neg(a, vs) =>
              val env = vs.zip(ws).toMap
              Node.Leaf(Atom(s"not ${a.rel.sym.name}", a.args.map(constant(_, env))))
            case Premise.Cmp(c, vs) =>
              val env = vs.zip(ws).toMap
              Node.Leaf(Atom(c.op.show, List(constant(c.l, env), constant(c.r, env))))
        }
        if current then instances += Instance(t(0).asInstanceOf[Id], children)

    // the exported program and its relation symbols
    def ruleTerm(t: Term): RTerm = t match
      case Term.Var(n) => RTerm.Variable(n)
      case other => RTerm.Constant(constant(other, Map.empty))
    def rule(pr: ProofRule): ExportedRule =
      val Term.App(RelRef.Sym(c), args) = pr.head: @unchecked
      val body = pr.rule.body.zip(pr.rel.premises).map {
        case (Formula.Not(a), Premise.Neg(_, vs)) =>
          val terms = a.args.map {
            case Term.Var(n) if !vs.contains(n) => RTerm.Constant(Var.display(n))
            case t => ruleTerm(t)
          }
          RAtom(s"not ${a.rel.sym.name}", terms, assumption = true)
        case (Formula.Cmp(op, l, r), _) => RAtom(op.show, List(ruleTerm(l), ruleTerm(r)), assumption = true)
        case (a: Formula.Atom, _) => RAtom(a.rel.sym.name, a.args.map(ruleTerm))
        case (f, _) => throw IllegalStateException(s"not in the exported fragment: ${ObjPrinter.formula(f)}")
      }
      ExportedRule(RAtom(c.name, args.map(ruleTerm)), body)
    val rules = unit.proofRules.map(rule)
    val symbols = rules.flatMap(r => r.head.symbol :: r.body.map(_.symbol)).toSet
    def exportable(sym: RelSym) = sym.kind != RelKind.Proof && !sym.isDerivation

    // the proofs: a breadth-first fixpoint, with the facts that have no instance as leaves
    val byHead = instances.groupBy(_.head)
    val usedBy = mutable.HashMap.empty[Id, mutable.ArrayBuffer[Instance]]
    for d <- instances; f <- d.facts do usedBy.getOrElseUpdate(f, mutable.ArrayBuffer.empty) += d
    val roots = (for
      (rel, tag) <- engine.store.zipWithIndex
      if exportable(rel.sym) && symbols(rel.sym.name)
      n <- rel.tuples.indices if rel.current(n)
    yield Id(tag, n)).toVector
    val universe = mutable.LinkedHashSet.from(roots)
    for d <- instances do
      universe += d.head
      universe ++= d.facts
    val proof = mutable.HashMap.empty[Id, Option[Instance]] // None: a leaf
    val missing = mutable.HashMap.from(instances.map(d => d -> d.facts.length))
    val queue = mutable.Queue.empty[Id]
    val settled = mutable.ArrayBuffer.empty[Id]
    def settle(f: Id, by: Option[Instance]): Unit =
      if !proof.contains(f) then
        proof(f) = by
        settled += f
        queue.enqueue(f)
    def propagate(): Unit =
      while queue.nonEmpty do
        for d <- usedBy.getOrElse(queue.dequeue(), Nil) do
          missing(d) -= 1
          if missing(d) == 0 then settle(d.head, Some(d))
    for d <- instances if d.facts.isEmpty do settle(d.head, Some(d))
    for f <- universe if !byHead.contains(f) do settle(f, None)
    propagate()
    // facts whose instances all depend on themselves: derived by a rule that is not exported, so leaves,
    // in the order they were derived
    for f <- universe if !proof.contains(f) do
      settle(f, None)
      propagate()
    Derivations(roots, proof, settled.toVector, rules)

  def apply(unit: CompilationUnit, prog: CoreProgram, engine: Engine, format: Format): Export =
    def factAtom(id: Id): Atom =
      val r = engine.store(id.rel)
      Atom(r.sym.name, r.tuples(id.n).toList.map(engine.show(_)))
    val ds = derivations(unit, prog, engine)
    val (roots, proof, rules) = (ds.roots, ds.proof, ds.rules)

    // the certificate
    val order = roots.sortBy(id => (engine.show(id), id.rel))
    val reached = mutable.LinkedHashSet.empty[Id]
    val trees = mutable.HashMap.empty[Id, Json]
    def tree(f: Id): Json = trees.getOrElseUpdate(
      f, {
        reached += f
        node(
          factAtom(f),
          proof(f).fold(Nil)(_.children.toList.map {
            case Node.Fact(id) => tree(id)
            case Node.Leaf(a) => node(a, Nil)
          })
        )
      }
    )
    def node(a: Atom, children: List[Json]) = Json.obj("node" -> Json.obj("label" -> atomJson(a), "children" -> Json.Arr(children)))
    val proofs = format match
      case Format.Trees => "trees" -> Json.Arr(order.toList.map(tree))
      case Format.OrderedGraph =>
        val index = mutable.HashMap.empty[Node, Int]
        val edges = mutable.ArrayBuffer.empty[Json]
        def visit(n: Node): Int = index.getOrElse(
          n, {
            val (a, preds) = n match
              case Node.Fact(id) =>
                reached += id
                (factAtom(id), proof(id).fold(Nil)(_.children.toList.map(visit)))
              case Node.Leaf(a) => (a, Nil)
            index(n) = edges.length
            edges += Json.obj("label" -> atomJson(a), "predecessors" -> Json.Arr(preds.map(i => Json.num(i.toLong))))
            edges.length - 1
          }
        )
        order.foreach(id => visit(Node.Fact(id)))
        "graph" -> Json.obj("edges" -> Json.Arr(edges.toList))
    val leaves = reached.toList.filter(proof(_).isEmpty)
    val (inputs, assumed) = leaves.partition(id => prog.directives(id.rel).input || prog.directives(id.rel).open)
    val inputRules = inputs.map(factAtom).sortBy(a => (a.symbol, a.terms.mkString(" "))).map(ExportedRule.fact)
    val assumedAtoms = assumed.sortBy(id => (engine.show(id), id.rel)).map(factAtom)
    val assumptionSymbols = rules.flatMap(_.body).filter(_.assumption).map(_.symbol).distinct.sorted
    val json = Json.obj(
      proofs,
      "program" -> Json.Arr((rules ++ inputRules).toList.map(_.json)),
      "hugin" -> Json.obj(
        "version" -> Json.num(Version),
        "format" -> Json.str(format.name),
        "assumptionSymbols" -> Json.Arr(assumptionSymbols.toList.map(Json.str)),
        "assumedFacts" -> Json.Arr(assumedAtoms.map(atomJson)),
        "omittedRules" -> Json.Arr(unit.proofOmitted.toList.map { (r, why) =>
          Json.obj("rule" -> Json.str(ObjPrinter.rule(r)), "at" -> Json.str(r.span.show), "reason" -> Json.str(why))
        })
      )
    )
    val warnings =
      unit.proofOmitted.toList.map { (r, why) =>
        s"warning: proof export: the rule `${ObjPrinter.rule(r)}` (${r.span.show}) is not exported, because $why; the facts it derives are assumed"
      } ++ (if assumed.isEmpty then Nil
            else
              List(
                s"warning: proof export: ${assumed.length} fact(s) have no exported derivation and are assumed (listed under `hugin.assumedFacts`)"
              )
      )
    Export(json, warnings)

  /** A term of an exported rule. */
  private[runtime] enum RTerm:
    case Variable(name: String)
    case Constant(text: String)
    def json: Json = this match
      case Variable(n) => Json.obj("variable" -> Json.str(n))
      case Constant(c) => Json.obj("constant" -> Json.str(c))

  private[runtime] final case class RAtom(symbol: String, terms: List[RTerm], assumption: Boolean = false):
    def json: Json = Json.obj("symbol" -> Json.str(symbol), "terms" -> Json.Arr(terms.map(_.json)))

  private[runtime] final case class ExportedRule(head: RAtom, body: List[RAtom]):
    def json: Json = Json.obj("head" -> head.json, "body" -> Json.Arr(body.map(_.json)))

  private object ExportedRule:
    /** The rule without body that states an input fact. */
    def fact(a: Atom): ExportedRule = ExportedRule(RAtom(a.symbol, a.terms.map(RTerm.Constant(_))), Nil)

  private def atomJson(a: Atom): Json =
    Json.obj("symbol" -> Json.str(a.symbol), "terms" -> Json.Arr(a.terms.map(c => Json.obj("constant" -> Json.str(c)))))
