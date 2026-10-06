package hugin.obj
package transform

import hugin.util.*
import hugin.compiler.*
import scala.collection.mutable

import hugin.obj.check.DepGraph
import hugin.obj.typing.Moding

/** Section 7.3: demand transformation (magic sets) for relations with declared modes. */
final class DemandPhase extends ObjProgramPhase:
  def phaseName = "demand"
  def description = "demand transformation for moded relations (Section 7.3)"

  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val facts = ctx.unit.facts
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
    val guarded = p.rules.flatMap { r =>
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
    val seen = mutable.HashSet.empty[Rule] // structural: spans are not part of a rule's equality
    val propagation = mutable.ArrayBuffer.empty[Rule]
    def emit(head: Term, prefix: List[Formula], span: Span, origin: Origin, expansions: List[Expansion], name: Option[String]): Unit =
      val r = Rule(name.map(n => s"$n^d"), List(head), prefix)(span, origin, expansions)
      if seen.add(r) then propagation += r
    // Calls of auxiliary relations (disjunctions inside aggregates) are deferred: their demand is built
    // from the part of the prefix that does not depend on the calling rule's head (see `auxDemand`).
    final case class AuxCall(head: Term, binds: Set[String], prefix: List[Formula], caller: Option[RelSym], rule: Rule)
    val auxCalls = mutable.ArrayBuffer.empty[AuxCall]
    def propagate(
        body: List[Formula],
        rule: Option[Rule],
        span: Span,
        origin: Origin,
        expansions: List[Expansion],
        name: Option[String]
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
                    val head = Term.App(RelRef.Sym(demand(c, m)), inputs(a.args, m))(a.span)
                    c.kind match
                      case RelKind.Auxiliary(_) if rule.isDefined =>
                        auxCalls += AuxCall(head, inputs(a.args, m).flatMap(Moding.vars).toSet, prefix, caller, rule.get)
                      case _ => emit(head, prefix, span, origin, expansions, name)
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
    for r <- guarded do propagate(r.body, Some(r), r.span, r.origin, r.expansions, r.name)
    for q <- p.queries do
      q.body match
        case List(Formula.Disj(alts)) => alts.foreach(a => propagate(a, None, q.span, q.origin, q.expansions, None))
        case b => propagate(b, None, q.span, q.origin, q.expansions, None)
    if auxCalls.nonEmpty then
      // The relations that depend on a caller, in the dependency graph without the demand of auxiliary
      // relations. Demand built only from other relations cannot close a cycle through the aggregate.
      val es = DepGraph.edges(p.copyWith(rules = guarded ++ propagation))
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
        emit(a.head, prefix, a.rule.span, a.rule.origin, a.rule.expansions, a.rule.name)
    p.rules = guarded ++ propagation
    p.rels = p.rels ++ demandRels.values

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
      if DepGraph.occurrences(List(f)).exists(o => excluded(o._1)) then (ks, b)
      else
        Moding.step(f, b) match
          case Right(b2) => (ks :+ f, b2)
          case Left(_) => (ks, b)
    }
    if binds.subsetOf(bound) then kept.toList else prefix
