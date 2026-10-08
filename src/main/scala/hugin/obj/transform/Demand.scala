package hugin.obj
package transform

import hugin.util.*
import hugin.compiler.*
import scala.collection.mutable

import hugin.obj.check.{DepEdge, DepGraph, Termination}
import hugin.obj.typing.Moding

/** Section 7.3: demand transformation (magic sets) for relations with declared modes. */
final class DemandPhase extends ObjProgramPhase:
  def phaseName = "demand"
  def description = "demand transformation for moded relations (Section 7.3)"

  /** The result of one demand transformation: the guarded and propagation rules, the demand relations,
   *  the call sites of every propagation rule (the call atom and the rule containing it), and the
   *  diagnostics (reported only for the transformation that is kept). */
  private final case class Transformed(
      rules: Vector[Rule],
      demandRels: Vector[RelSym],
      sites: Vector[(Rule, List[(Formula.Atom, Rule)])],
      diagnostics: Vector[Diagnostic]
  )

  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    // Per-call-site demand (see docs/NOTES.md, "Demand per call site"): all calls of a moded relation share
    // its demand relation, so a call whose demand reads a relation depending on the callee's answers puts
    // that relation into the callee's component. If this closes a cycle through negation or aggregation,
    // the offending call sites get their own copy of the callee (with its own demand relation), and the
    // transformation is repeated; if cycles remain, the shared transformation is kept (E0601).
    val first = transform(p.rules)
    var result = first
    var rules = p.rules
    val copies = mutable.ArrayBuffer.empty[RelSym]
    var round = 0
    var sites = cyclicSites(p, result, copies.toSet)
    while !sites.isEmpty && round < DemandPhase.MaxRounds do
      rules = specialize(rules, sites, copies)
      result = transform(rules)
      round += 1
      sites = cyclicSites(p, result, copies.toSet)
    val kept = if round > 0 && negativeCycle(p, result, copies.toSet) then first else result
    kept.diagnostics.foreach(ctx.report)
    p.rules = kept.rules
    p.rels = p.rels ++ (if kept eq first then Nil else copies) ++ kept.demandRels

  /** The demand transformation of `rules` (Section 7.3). */
  private def transform(rules: Vector[Rule])(using Context): Transformed =
    val p = ctx.unit.prog.nn
    val facts = ctx.unit.facts
    val diagnostics = mutable.ArrayBuffer.empty[Diagnostic]
    val demandRels = mutable.LinkedHashMap.empty[(RelSym, Mode), RelSym]
    def demand(c: RelSym, m: Mode): RelSym =
      demandRels.getOrElseUpdate(
        (c, m), {
          val d = RelSym(s"${c.name}^d[${m.show}]", RelKind.Demand(c, m), c.span, c.origin)
          d.cols = c.cols.zip(m.inputs).filter(_._2).map(_._1)
          d
        }
      )
    def inputs(args: List[Term], m: Mode): List[Term] = args.zip(m.inputs).filter(_._2).map(_._1)

    // 1. guarding
    val guarded = rules.flatMap { r =>
      r.heads match
        case List(h @ Term.App(RelRef.Sym(c), args)) if facts.hasModes(c) =>
          facts.modes(c).map { (m, _) =>
            val g = Formula.Atom(RelRef.Sym(demand(c, m)), inputs(args, m), None)(h.span)
            val nr = r.withParts(body = g :: r.body)
            val gt = ctx.unit.varTypes.get(r)
            if gt != null then ctx.unit.varTypes.put(nr, gt)
            nr
          }
        case _ => List(r)
    }
    // 2. propagation
    val propagation = mutable.LinkedHashMap.empty[Rule, mutable.ListBuffer[(Formula.Atom, Rule)]] // structural keys
    def emit(head: Term, prefix: List[Formula], span: Span, origin: Origin, expansions: List[Expansion], name: Option[String])(
        site: Option[(Formula.Atom, Rule)]
    ): Unit =
      val r = Rule(name.map(n => s"$n^d"), List(head), prefix)(span, origin, expansions)
      propagation.getOrElseUpdate(r, mutable.ListBuffer.empty) ++= site
    // Calls of auxiliary relations (disjunctions inside aggregates) are deferred: their demand is built
    // from the part of the prefix that does not depend on the calling rule's head (see `auxDemand`).
    final case class AuxCall(head: Term, binds: Set[String], prefix: List[Formula], caller: Option[RelSym], rule: Rule, atom: Formula.Atom)
    val auxCalls = mutable.ArrayBuffer.empty[AuxCall]
    val reported = mutable.HashSet.empty[Span] // E0504, once per term (a rule is guarded once per mode)
    def propagate(
        body: List[Formula],
        rule: Option[Rule],
        span: Span,
        origin: Origin,
        expansions: List[Expansion],
        name: Option[String],
        inItem: Diagnostic => Diagnostic
    ): Unit =
      val caller = rule.flatMap(_.heads.collectFirst { case Term.App(RelRef.Sym(c), _) => c })
      Moding.canonical(body, Set.empty) match
        case Left(_) => // reported by `moding`
        case Right((ordered, _)) =>
          def walk(prefix: List[Formula], fs: List[Formula], b: Set[String]): Unit = fs match
            case Nil =>
            case f :: rest =>
              def call(a: Formula.Atom): Unit =
                val c = a.rel.sym
                if facts.hasModes(c) then
                  Moding.firstApplicable(c, a.args, b).foreach { m =>
                    for t <- inputs(a.args, m).flatMap(DepGraph.factTerms).headOption if reported.add(t.span) do
                      diagnostics += inItem(factInInput(c, m, t))
                    val head = Term.App(RelRef.Sym(demand(c, m)), inputs(a.args, m))(a.span)
                    c.kind match
                      case RelKind.Auxiliary(_) if rule.isDefined =>
                        auxCalls += AuxCall(head, inputs(a.args, m).flatMap(Moding.vars).toSet, prefix, caller, rule.get, a)
                      case _ => emit(head, prefix, span, origin, expansions, name)(rule.map(a -> _))
                  }
              f match
                case a: Formula.Atom => call(a)
                case Formula.Not(a) => call(a)
                case Formula.Agg(_, _, _, ib) =>
                  Moding.canonical(ib, b) match
                    case Right((iordered, _)) => walk(prefix, iordered, b)
                    case Left(_) =>
                case _ =>
              val b2 = Moding.step(f, b).getOrElse(b)
              walk(prefix :+ f, rest, b2)
          walk(Nil, ordered, Set.empty)
    for r <- guarded do propagate(r.body, Some(r), r.span, r.origin, r.expansions, r.name, Diag.rule(r))
    for q <- p.queries do
      q.body match
        case List(Formula.Disj(alts)) => alts.foreach(a => propagate(a, None, q.span, q.origin, q.expansions, None, Diag.query(q)))
        case b => propagate(b, None, q.span, q.origin, q.expansions, None, Diag.query(q))
    if auxCalls.nonEmpty then
      // The relations that depend on a caller, in the dependency graph without the demand of auxiliary
      // relations. Demand built only from other relations cannot close a cycle through the aggregate.
      val es = DepGraph.edges(p.copyWith(rules = guarded ++ propagation.keys))
      val pred = es.groupBy(_.to).view.mapValues(_.map(_.from)).toMap
      val dependents = mutable.HashMap.empty[RelSym, Set[RelSym]]
      def dependentsOf(c: RelSym): Set[RelSym] = dependents.getOrElseUpdate(
        c, {
          val seen = mutable.HashSet(c)
          val todo = mutable.Stack(c)
          while todo.nonEmpty do pred.getOrElse(todo.pop(), Nil).foreach(x => if seen.add(x) then todo.push(x))
          seen.toSet
        }
      )
      for a <- auxCalls do
        val prefix = a.caller.map(c => auxDemand(a.prefix, a.binds, dependentsOf(c))).getOrElse(a.prefix)
        emit(a.head, prefix, a.rule.span, a.rule.origin, a.rule.expansions, a.rule.name)(Some(a.atom -> a.rule))
    Transformed(
      guarded ++ propagation.keys,
      demandRels.values.toVector,
      propagation.toVector.map((r, s) => (r, s.toList)),
      diagnostics.toVector
    )

  /** Components of the transformed program and the indices of those with an internal negative edge. */
  private def negativeComponents(p: ObjProgram, t: Transformed, copies: Set[RelSym])(using
      ProgramFacts
  ): (List[DepEdge], Map[RelSym, Int], Set[Int]) =
    val es = DepGraph.edges(p.copyWith(rules = t.rules))
    val succ = es.groupBy(_.from).view.mapValues(_.map(_.to).distinct).toMap
    val nodes = (p.rels ++ copies ++ t.demandRels).distinct
    val compOf = Graphs.components(nodes, (r: RelSym) => succ.getOrElse(r, Nil)).zipWithIndex.flatMap((c, i) => c.map(_ -> i)).toMap
    val bad = es.collect { case e if e.negative && compOf.get(e.from).exists(compOf.get(e.to).contains) => compOf(e.from) }.toSet
    (es, compOf, bad)

  private def negativeCycle(p: ObjProgram, t: Transformed, copies: Set[RelSym])(using ProgramFacts): Boolean =
    negativeComponents(p, t, copies)._3.nonEmpty

  /** The call sites to give their own copy of the callee: calls of a plain moded relation `c` from a rule
   *  of another relation whose propagation rule (head `c^d`) lies in a component with a cycle through
   *  negation and reads that component (the edge `c^d → X` of the cycle, `X` depending on `c`'s answers).
   *  Calls of copies are not copied again. */
  private def cyclicSites(p: ObjProgram, t: Transformed, copies: Set[RelSym])(using
      ProgramFacts
  ): java.util.IdentityHashMap[Formula.Atom, RelSym] =
    val out = java.util.IdentityHashMap[Formula.Atom, RelSym]()
    val (_, compOf, bad) = negativeComponents(p, t, copies)
    if bad.nonEmpty then
      for
        (dr, sites) <- t.sites
        d <- Termination.headRel(dr).toList
        ci <- compOf.get(d).toList if bad(ci)
        c <- d.kind match
          case RelKind.Demand(c, _) if c.kind == RelKind.Plain && !copies(c) => List(c)
          case _ => Nil
        if DepGraph.occurrences(dr.body).exists(o => compOf.get(o._1).contains(ci))
        (atom, caller) <- sites if !Termination.headRel(caller).contains(c)
      do out.put(atom, c)
    out

  /** Gives every call site in `sites` its own copy `c#k` of the callee `c`: the rules of `c` with `c`
   *  renamed (also in its recursive calls), the directives of `c` (modes, measure, `%open`),
   *  and the call atom renamed. A copy derives exactly the answers of `c` for the demands of its call
   *  site, so the answers at every call site are unchanged. */
  private def specialize(rules: Vector[Rule], sites: java.util.IdentityHashMap[Formula.Atom, RelSym], copies: mutable.ArrayBuffer[RelSym])(
      using Context
  ): Vector[Rule] =
    import scala.jdk.CollectionConverters.*
    val renaming = java.util.IdentityHashMap[Formula.Atom, RelSym]()
    val added = mutable.ArrayBuffer.empty[Rule]
    for (atom, c) <- sites.asScala.toList.sortBy((a, _) => (a.span.source.path, a.span.start, a.span.end)) do
      val k = copies.length + 1
      val copy = RelSym(s"${c.name}#$k", c.kind, c.span, c.origin)
      copy.cols = c.cols
      copy.instanceOf = c.instanceOf
      copies += copy
      ctx.unit.facts = ctx.unit.facts.updated(copy)(_ =>
        ctx.unit.facts(c).copy(input = false, output = false, derivations = false, nameHint = None)
      )
      renaming.put(atom, copy)
      for r <- rules if Termination.headRel(r).contains(c) do
        val nr = Rule(
          None,
          r.heads.map(DemandPhase.renameTerm(c, copy)),
          r.body.map(DemandPhase.renameAtoms(a => Option.when(a.rel.sym == c)(copy)))
        )(
          r.span,
          r.origin,
          r.expansions
        )
        val gt = ctx.unit.varTypes.get(r)
        if gt != null then ctx.unit.varTypes.put(nr, gt)
        added += nr
    val rewritten = rules.map { r =>
      if !r.body.exists(DemandPhase.atoms(_).exists(renaming.containsKey)) then r
      else
        val nr = r.withParts(body = r.body.map(DemandPhase.renameAtoms(a => Option(renaming.get(a)))))
        val gt = ctx.unit.varTypes.get(r)
        if gt != null then ctx.unit.varTypes.put(nr, gt)
        nr
    }
    rewritten ++ added

  /** E0504: a fact-constructor term `t` in an input of a call of `c` with mode `m`. The demand rule would
   *  build `t` as a fact, so `%mode` would change the database; inputs may contain data terms and
   *  variables (bound values, whose fact-constructor subterms are facts already). This keeps the
   *  guarantee that `%mode` adds facts only to the moded relation and its demand relations. */
  private def factInInput(c: RelSym, m: Mode, t: Term.App)(using facts: ProgramFacts): Diagnostic =
    val modeAt = facts.modes(c).find(_._1 == m).map(_._2)
    DemandError.FactInModedInput(c, m, modeAt, t, t.rel.sym).toDiagnostic

  /** The demand of an auxiliary relation for a disjunction inside an aggregate (see `Disjunctions`):
   *  the formulas of `prefix` (in canonical order) that do not mention a relation of `excluded` (the
   *  relations that depend on the calling rule's head) and are well-moded without the others, provided
   *  they bind the demanded inputs `binds`; otherwise the whole prefix. A subset of the prefix holds
   *  whenever the prefix holds, so every binding of the inputs that arises at the call is demanded (the
   *  aggregate sees all answers for it); the auxiliary relation then depends only on relations evaluated
   *  before the caller, and the aggregate's negative edge cannot close a cycle (issue #1, F1).
   */
  private def auxDemand(prefix: List[Formula], binds: Set[String], excluded: Set[RelSym])(using ProgramFacts): List[Formula] =
    val (kept, bound) = prefix.foldLeft((Vector.empty[Formula], Set.empty[String])) { case ((ks, b), f) =>
      if DepGraph.occurrences(List(f), bound = b).exists(o => excluded(o._1)) then (ks, b)
      else
        Moding.step(f, b) match
          case Right(b2) => (ks :+ f, b2)
          case Left(_) => (ks, b)
    }
    if binds.subsetOf(bound) then kept.toList else prefix

object DemandPhase:
  /** Rounds of per-call-site specialization (each round copies the callee for the offending sites). */
  val MaxRounds = 4

  /** The atoms of a formula (positive, negated, in aggregates and disjunctions). */
  def atoms(f: Formula): List[Formula.Atom] = f match
    case a: Formula.Atom => List(a)
    case Formula.Not(a) => List(a)
    case Formula.Agg(_, _, _, b) => b.flatMap(atoms)
    case Formula.Disj(alts) => alts.flatten.flatMap(atoms)
    case _ => Nil

  /** Replaces the relation of the atoms for which `to` gives one. */
  def renameAtoms(to: Formula.Atom => Option[RelSym])(f: Formula): Formula =
    def atom(a: Formula.Atom): Formula.Atom = to(a).map(c => Formula.Atom(RelRef.Sym(c), a.args, a.as)(a.span)).getOrElse(a)
    f match
      case a: Formula.Atom => atom(a)
      case n @ Formula.Not(a) => Formula.Not(atom(a))(n.span)
      case g @ Formula.Agg(res, kind, t, b) => Formula.Agg(res, kind, t, b.map(renameAtoms(to)))(g.span)
      case d @ Formula.Disj(alts) => Formula.Disj(alts.map(_.map(renameAtoms(to))))(d.span)
      case other => other

  /** Renames the head relation `c` of a rule head to `to`. */
  def renameTerm(c: RelSym, to: RelSym)(t: Term): Term = t match
    case a @ Term.App(RelRef.Sym(`c`), as) => Term.App(RelRef.Sym(to), as)(a.span)
    case other => other
