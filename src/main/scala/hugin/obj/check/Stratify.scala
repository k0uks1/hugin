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
      ctx.report(Diag.rule(e.rule)(d))

    // Facts constructed through nested heads in relations of *earlier* components can be missed by
    // readers evaluated in between (a gap in the ordering argument of Proposition 8.8); warn about it.
    val readers = p.rules.flatMap(r => DepGraph.occurrences(r.body).map(o => (o._1, r))).groupBy(_._1).view.mapValues(_.map(_._2)).toMap
    if ctx.settings.lint then
      for r <- p.rules; h <- r.heads.collectFirst { case Term.App(RelRef.Sym(c), _) if !c.isDerivation => c } do
        val hi = compOf(h)
        for t <- DepGraph.newHeadConstructors(r); c = t.rel.sym if compOf(c) < hi do
          val affected = readers.getOrElse(c, Vector.empty).filter(rr =>
            (rr ne r) && rr.heads.exists {
              case Term.App(RelRef.Sym(x), _) => compOf(x) >= compOf(c) && compOf(x) <= hi
              case _ => false
            }
          )
          affected.headOption.foreach { rr =>
            val reader = rr.heads.collectFirst { case Term.App(RelRef.Sym(x), _) => x.name }.getOrElse("?")
            ctx.report(Diag.rule(r)(Diagnostic.warning(
              "W0004",
              s"facts of `${c.name}` constructed here may be missed by `$reader`",
              t.span,
              s"`${c.name}` is evaluated before `${h.name}`"
            )
              .withLabel(rr.span, s"`$reader` reads `${c.name}`")
              .withNote("nested head constructors create facts of an earlier component after it was evaluated (see docs/NOTES.md)")))
          }

  override def show(using Context): String =
    ctx.unit.components.zipWithIndex.map((c, i) => s"component $i: ${c.map(_.name).mkString(", ")}").mkString("\n")
