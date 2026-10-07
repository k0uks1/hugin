package hugin.obj
package check

import hugin.util.*
import hugin.compiler.*
import scala.collection.mutable

/** Phase: stratification (Section 6.4). Computes the evaluation order of components. */
final class StratifyPhase extends Phase:
  def phaseName = "stratify"
  def description = "dependency graph, components and stratification (Section 6.4)"

  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val es = DepGraph.edges(p)
    val succ = es.groupBy(_.from).view.mapValues(_.map(_.to).distinct).toMap
    val comps = Graphs.components(p.rels.toList, (r: RelSym) => succ.getOrElse(r, Nil))
    ctx.unit.components = comps
    val compOf = comps.zipWithIndex.flatMap((c, i) => c.map(_ -> i)).toMap
    val reported = mutable.HashSet.empty[Int]
    for e <- es if e.negative && compOf(e.from) == compOf(e.to) && reported.add(compOf(e.from)) do
      // find a path back from `e.to` to `e.from` inside the component
      val inComp = es.filter(x => compOf(x.from) == compOf(e.from) && compOf(x.to) == compOf(e.from))
      val path = Graphs.shortestPath(inComp, (x: DepEdge) => x.from, (x: DepEdge) => x.to, e.to, e.from)
      val cycle = (e :: path).map(x => (if x.negative then "not " else "") + x.to.name)
      var d =
        Diagnostic.error("E0601", "stratification cycle through negation", e.span, s"`${e.from.name}` depends negatively on `${e.to.name}`")
      d = d.withNote(s"cycle: ${e.from.name} -> ${cycle.mkString(" -> ")}")
      for x <- path.take(3) do d = d.withLabel(x.span, s"`${x.from.name}` depends on `${x.to.name}`")
      d = d.withNote("negation and aggregation must not occur in a recursive cycle (Section 6.4)")
      // an edge from a fact constructor asserted in the head of another relation's rule (Proposition 8.8)
      (e :: path).find(x => x.rule.heads.headOption.exists { case Term.App(RelRef.Sym(h), _) => h != x.from; case _ => false })
        .foreach { x =>
          val h = x.rule.heads.head match
            case Term.App(RelRef.Sym(h), _) => h.name
            case _ => "?"
          d = d.withNote(
            s"a rule of `$h` asserts facts of `${x.from.name}` in its head, so `${x.from.name}` depends on what the rule reads (Proposition 8.8, see docs/NOTES.md)"
          )
        }
      // the demand of a disjunction inside an aggregate reads the caller (see `DemandPhase.auxDemand`)
      (e :: path).map(_.to.kind).collectFirst { case RelKind.Demand(aux, _) if aux.kind.isInstanceOf[RelKind.Auxiliary] => aux }.foreach {
        aux =>
          d = d.withNote(
            s"`${aux.name}` stands for a disjunction inside an aggregate; its demand needs the disjunction's outer variables, which are bound only by relations that depend on `${e.from.name}`"
          )
          d = d.withHelp(
            s"bind the disjunction's outer variables with relations evaluated before `${e.from.name}`, or define the disjunction as a relation with one rule per alternative"
          )
      }
      ctx.report(Diag.rule(e.rule)(d))

    // Proposition 8.8: a rule of `h` asserting a fact-constructor term `c t̄` of an earlier component gets a
    // copy `c t̄ :- body` evaluated in `c`'s component, so `c` is complete before its readers run.
    val split = StratifyPhase.splitRules(p.rules, compOf)
    split.foreach(ctx.unit.splitRules.add)
    p.rules = p.rules ++ split

  override def show(using Context): String =
    ctx.unit.components.zipWithIndex.map((c, i) => s"component $i: ${c.map(_.name).mkString(", ")}").mkString("\n")

object StratifyPhase:
  /** The split rules of Proposition 8.8 (see docs/NOTES.md, "Nested head constructors and the evaluation
   *  order"). A rule `h … (c t̄) … :- body` asserts the fact `c t̄` besides its own fact (`subfact_F`,
   *  [[DepGraph.assertedHeadConstructors]]). The dependency graph already lets `c` depend on everything
   *  `body` reads (Section 6.4, as extended in "Data and fact constructors"), so the rule `c t̄ :- body`
   *  has exactly the edges of the graph and changes neither the components nor the stratification. If
   *  `c`'s component comes before `h`'s, that rule is added and evaluated in `c`'s component: when it is
   *  complete, `body`'s relations are complete too (they are `c`'s dependencies), so the split rule
   *  derives every `c t̄` the original rule will assert later, and the later assertions add nothing.
   *  Hence every component is complete after its evaluation and the result is the least model.
   *  Derivation rules are not split: the terms in their heads are facts derived by the rule they
   *  describe (and guarded input columns are excluded by `assertedHeadConstructors`). */
  def splitRules(rules: Vector[Rule], compOf: Map[RelSym, Int]): Vector[Rule] =
    for
      r <- rules
      h <- r.heads.collectFirst { case Term.App(RelRef.Sym(c), _) if !c.isDerivation => c }.toVector
      t <- DepGraph.assertedHeadConstructors(r).distinct.toVector
      if compOf.get(t.rel.sym).exists(ci => compOf.get(h).exists(ci < _))
    yield Rule(None, List(t), r.body)(r.span, r.origin, r.expansions)
