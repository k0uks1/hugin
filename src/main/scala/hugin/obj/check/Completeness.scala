package hugin.obj
package check

import hugin.util.*
import hugin.compiler.*
import scala.collection.mutable

/** Phase: completeness discipline (Section 6.5). */
final class CompletenessPhase extends Phase:
  /** Relations that may be incomplete (for `--print-after completeness`). */
  private var incomplete: Set[RelSym] = Set.empty

  def phaseName = "completeness"
  def description = "incomplete relations are never negated or aggregated over (Definition 6.6)"

  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val es = DepGraph.edges(p)
    // reason for incompleteness, propagated backwards along positive edges
    val why = mutable.LinkedHashMap.empty[RelSym, String]
    for r <- p.rels do
      if r.isOpen then why(r) = s"`${r.name}` is declared %open"
      else if r.isPartial then why(r) = s"`${r.name}` is declared %partial"
    var changed = true
    while changed do
      changed = false
      for e <- es if !e.negative && why.contains(e.to) && !why.contains(e.from) do
        why(e.from) = s"`${e.from.name}` depends positively on `${e.to.name}`; ${why(e.to)}"
        changed = true
    incomplete = why.keySet.toSet
    for e <- es if e.negative && why.contains(e.to) do
      ctx.report(Diag.rule(e.rule)(Diagnostic.error(
        "E0602",
        s"negation or aggregation over the incomplete relation `${e.to.name}`",
        e.span,
        "incomplete relation used negatively"
      )
        .withNote(why(e.to))
        .withNote("the absence of a fact of an incomplete relation means unknown, not false (Definition 6.6)")))
    for q <- p.queries; (r, neg, sp) <- DepGraph.occurrences(q.body) if neg && why.contains(r) do
      ctx.report(Diag.query(q)(Diagnostic.error(
        "E0602",
        s"query negates or aggregates over the incomplete relation `${r.name}`",
        sp,
        "used negatively"
      )
        .withNote(why(r))
        .withNote("queries may mention incomplete relations only positively (Section 8.5)")))

  override def show(using Context): String =
    s"incomplete: ${incomplete.map(_.name).toList.sorted.mkString(", ")}"
