package hugin.core
package elab

import scala.collection.mutable

/** Names not in `taken0` nor given before: `fresh(base)` is the first of `base` (if free), `base1`,
 *  `base2`, … that is not taken. Each base resumes its search where the last one stopped: names are only
 *  added, so the candidates before it are still taken (searching from 1 every time was quadratic in the
 *  number of names of a base, which the split records of a large family made visible). */
final class FreshNames(taken0: Iterable[String]):
  private val taken = mutable.Set.from(taken0)
  private val from = mutable.HashMap.empty[String, Int]
  private def candidate(base: String, k: Int) = if k == 1 && !taken(base) then base else s"$base$k"
  def apply(base: String): String =
    val k = Iterator.from(from.getOrElse(base, 1)).find(k => !taken(candidate(base, k))).get
    val name = candidate(base, k)
    from(base) = k
    taken += name
    name
