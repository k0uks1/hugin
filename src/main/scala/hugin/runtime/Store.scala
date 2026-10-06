package hugin.runtime

import hugin.obj.RelSym
import scala.collection.mutable

/** A tuple key with structural equality. */
final class Key(val ws: Array[Any]):
  override def hashCode: Int = java.util.Arrays.hashCode(ws.asInstanceOf[Array[AnyRef]])
  override def equals(o: Any): Boolean = o match
    case k: Key => java.util.Arrays.equals(ws.asInstanceOf[Array[AnyRef]], k.ws.asInstanceOf[Array[AnyRef]])
    case _ => false

/** The values of one relation (Section 9.4), with the distinction between values and facts:
 *
 *  - a *value* is an interned tuple with an identity `n` ([[tuples]]`(n)`); every constructed term is one;
 *  - a *fact* is a value that is asserted, i.e. belongs to the database. Values built by ordinary rule
 *    heads (and their nested values) are facts; values built only as inputs of moded calls are *probes*
 *    (interned, not asserted).
 *
 *  Scans read facts only, in the order they were asserted ([[facts]]), so the old/delta/full windows of
 *  semi-naive evaluation are ranges of positions in that order and a probe that is asserted later enters
 *  the delta like any new fact. Hash indexes on bound columns hold positions of facts. Dereferencing an
 *  identity and looking up a value see all values. */
final class Relation(val tag: Int, val sym: RelSym, val arity: Int, indexCols: Set[Vector[Int]]):
  /** All values, by identity. */
  val tuples: mutable.ArrayBuffer[Array[Any]] = mutable.ArrayBuffer.empty

  /** Identities of the facts, in the order they were asserted. */
  val facts: mutable.ArrayBuffer[Int] = mutable.ArrayBuffer.empty

  private val interned = mutable.HashMap.empty[Key, Int]
  private val asserted = mutable.BitSet.empty
  private val indexes: Map[Vector[Int], mutable.HashMap[Key, mutable.ArrayBuffer[Int]]] =
    indexCols.map(c => c -> mutable.HashMap.empty[Key, mutable.ArrayBuffer[Int]]).toMap

  /** The number of facts. */
  def size: Int = facts.length

  def isFact(n: Int): Boolean = asserted(n)

  /** The identity of a value, fact or probe; -1 if the tuple was never interned. */
  def lookup(t: Array[Any]): Int = interned.getOrElse(Key(t), -1)

  /** Interns a tuple and, if `assert`, makes it a fact. Returns its identity. */
  def intern(t: Array[Any], assert: Boolean): Int =
    val k = Key(t)
    val n = interned.getOrElseUpdate(k, { tuples += t; tuples.length - 1 })
    if assert && !asserted(n) then
      asserted += n
      val pos = facts.length
      facts += n
      for (cols, idx) <- indexes do
        idx.getOrElseUpdate(Key(cols.map(t(_)).toArray), mutable.ArrayBuffer.empty) += pos
    n

  /** Positions (in [[facts]]) of the facts with the given values in the given columns, ascending. */
  def index(cols: Vector[Int]): mutable.HashMap[Key, mutable.ArrayBuffer[Int]] = indexes(cols)
