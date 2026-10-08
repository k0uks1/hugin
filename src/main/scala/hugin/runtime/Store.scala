package hugin.runtime

import hugin.obj.RelSym
import hugin.syntax.Bound
import scala.collection.mutable

/** A tuple key with structural equality. */
final class Key(val ws: Array[Any]):
  override def hashCode: Int = java.util.Arrays.hashCode(ws.asInstanceOf[Array[AnyRef]])
  override def equals(o: Any): Boolean = o match
    case k: Key => java.util.Arrays.equals(ws.asInstanceOf[Array[AnyRef]], k.ws.asInstanceOf[Array[AnyRef]])
    case _ => false

/** The interned tuples of one relation symbol (Section 9.4): tuple `n` has the identity `(tag, n)`.
 *
 *  - For a relation of F (plain relations, constructors and structs, auxiliary and derivation
 *    relations) interned means asserted: every tuple is a fact, tuples are kept in assertion
 *    order, so the old/delta/full windows of semi-naive evaluation are ranges of identities, and hash
 *    indexes on bound columns hold identities.
 *  - For a relation with a bound column (docs/REDESIGN.md §5.2) only the best tuple per key is current;
 *    replaced tuples stay in the table (so windows remain identity ranges) but are invisible. */
final class Relation(val tag: Int, val sym: RelSym, val arity: Int, indexCols: Set[Vector[Int]]):
  val tuples: mutable.ArrayBuffer[Array[Any]] = mutable.ArrayBuffer.empty
  private val interned = mutable.HashMap.empty[Key, Int]
  private val indexes: Map[Vector[Int], mutable.HashMap[Key, mutable.ArrayBuffer[Int]]] =
    indexCols.map(c => c -> mutable.HashMap.empty[Key, mutable.ArrayBuffer[Int]]).toMap

  /** The bound column of the relation (its last column), if it has one: then [[intern]] keeps one tuple
   *  per key, the one with the best value; a better value is appended as a new tuple and the old one is
   *  marked replaced (see [[replacedBy]]). */
  val bound: Option[Bound] = sym.boundColumn
  val isBound: Boolean = bound.isDefined

  /** For a bound relation: the identity of the tuple that replaced tuple `n` (`Int.MaxValue` while it
   *  is current). Identities stay in insertion order, so a version window `[lo, hi)` sees tuple `n` iff
   *  `lo <= n < hi` and it was not replaced before `hi` ([[visible]]). */
  private val replacedBy = mutable.ArrayBuffer.empty[Int]

  /** The number of tuples. */
  def size: Int = tuples.length

  /** Whether tuple `n` is current in a window ending at `hi`: always for a relation without bound
   *  column, otherwise if it was not replaced by a tuple below `hi`. */
  inline def visible(n: Int, hi: Int): Boolean = !isBound || replacedBy(n) >= hi

  /** Whether tuple `n` is current (the best value of its key, or a tuple of a relation without bound column). */
  def current(n: Int): Boolean = visible(n, Int.MaxValue)

  /** Whether a bound relation has a current tuple for `key` (the tuple without its bound column). */
  def hasKey(key: Key): Boolean = interned.contains(key)

  /** The identity of a tuple; -1 if it was never interned (for a bound relation: if it is not current). */
  def lookup(t: Array[Any]): Int =
    if isBound then
      val n = interned.getOrElse(Key(t.init), -1)
      if n >= 0 && tuples(n)(arity - 1) == t(arity - 1) then n else -1
    else interned.getOrElse(Key(t), -1)

  /** Interns a tuple (for a relation of F: asserts it). Returns its identity. For a bound relation the
   *  tuple is kept only if its value is better than the key's current one; the result is the identity of
   *  the key's current tuple. */
  def intern(t: Array[Any]): Int =
    if isBound then improve(t)
    else
      val k = Key(t)
      interned.get(k) match
        case Some(n) => n
        case None =>
          val n = append(t)
          interned(k) = n
          n

  /** The current tuple of the key of `t` after offering `t`'s value. */
  private def improve(t: Array[Any]): Int =
    val k = Key(t.init)
    interned.get(k) match
      case Some(n) if !better(t(arity - 1), tuples(n)(arity - 1)) => n
      case old =>
        val m = append(t)
        old.foreach(n => replacedBy(n) = m)
        interned(k) = m
        m

  /** Whether `v` is a better value than `w` for the bound column. */
  def better(v: Any, w: Any): Boolean =
    ExtendedInt.compare(v, w).exists(c => if bound.contains(Bound.Min) then c < 0 else c > 0)

  private def append(t: Array[Any]): Int =
    val n = tuples.length
    tuples += t
    if isBound then replacedBy += Int.MaxValue
    for (cols, idx) <- indexes do idx.getOrElseUpdate(Key(cols.map(t(_)).toArray), mutable.ArrayBuffer.empty) += n
    n

  /** Identities of the tuples with the given values in the given columns, ascending. */
  def index(cols: Vector[Int]): mutable.HashMap[Key, mutable.ArrayBuffer[Int]] = indexes(cols)
