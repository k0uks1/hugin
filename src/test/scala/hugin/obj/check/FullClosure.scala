package hugin.obj
package check

import scala.collection.mutable

/** The size-change check as it was before issue #65, kept as the reference for the antichain closure of
 *  [[SizeChange.check]]: the full composition closure, at most `cap` graphs, with the idempotent test
 *  of Lee, Jones and Ben-Amram ([[SizeChange.Graph.descends]]). */
object FullClosure:
  /** The old cap. */
  val OldCap = 4000

  /** `None` if the closure exceeds `cap` graphs; otherwise whether the component passes, and the size of
   *  the closure. */
  def check(base: Vector[SizeChange.Step], cap: Int = OldCap): Option[(Boolean, Int)] =
    val byFrom = base.groupBy(_.from)
    val seen = mutable.HashSet.empty[(RelSym, RelSym, SizeChange.Graph)]
    val work = mutable.Queue.from(base.map(s => (s.from, s.to, s.graph)))
    while work.nonEmpty && seen.size <= cap do
      val key @ (from, to, g) = work.dequeue()
      if seen.add(key) then for s <- byFrom.getOrElse(to, Vector.empty) do work.enqueue((from, s.to, g.andThen(s.graph)))
    Option.when(seen.size <= cap)(
      (!seen.exists((from, to, g) => from == to && g.idempotent && !g.descends(from.arity)), seen.size)
    )
