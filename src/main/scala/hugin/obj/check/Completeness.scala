package hugin.obj
package check

import hugin.util.*
import hugin.compiler.*
import scala.collection.mutable

/** Phase: completeness discipline (Section 6.5). */
final class CompletenessPhase extends Phase:
  def phaseName = "completeness"
  def description = "incomplete relations are never negated or aggregated over (Definition 6.6)"

  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val es = DepGraph.edges(p)
    // reason for incompleteness, propagated backwards along positive edges
    val why = mutable.LinkedHashMap.empty[RelSym, Incompleteness]
    val facts = ctx.unit.facts
    for r <- p.rels do
      if facts(r).open then why(r) = Incompleteness.Open(r)
    var changed = true
    while changed do
      changed = false
      for e <- es if !e.negative && why.contains(e.to) && !why.contains(e.from) do
        why(e.from) = Incompleteness.Via(e.from, e.to, e.span, why(e.to))
        changed = true
    ctx.unit.incomplete = why.keySet.toSet
    for e <- es if e.negative && why.contains(e.to) do
      ctx.report(Diag.rule(e.rule)(CheckError.NegatedIncomplete(e.to, e.span, NegSite.InRule, why(e.to)).toDiagnostic))
    for q <- p.queries; (r, neg, sp) <- DepGraph.occurrences(q.body) if neg && why.contains(r) do
      ctx.report(Diag.query(q)(CheckError.NegatedIncomplete(r, sp, NegSite.InQuery, why(r)).toDiagnostic))

  override def show(using Context): String =
    s"incomplete: ${ctx.unit.incomplete.map(_.name).toList.sorted.mkString(", ")}"
