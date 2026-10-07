package hugin.runtime

import hugin.obj.RelSym
import scala.collection.mutable

/** A tuple key with structural equality. */
final class Key(val ws: Array[Any]):
  override def hashCode: Int = java.util.Arrays.hashCode(ws.asInstanceOf[Array[AnyRef]])
  override def equals(o: Any): Boolean = o match
    case k: Key => java.util.Arrays.equals(ws.asInstanceOf[Array[AnyRef]], k.ws.asInstanceOf[Array[AnyRef]])
    case _ => false

/** The interned tuples of one relation symbol (Section 9.4): tuple `n` has the identity `(tag, n)`.
 *
 *  - For a relation of F (plain relations, fact constructors and fact structs, demand, auxiliary and
 *    derivation relations) interned means asserted: every tuple is a fact, tuples are kept in assertion
 *    order, so the old/delta/full windows of semi-naive evaluation are ranges of identities, and hash
 *    indexes on bound columns hold identities.
 *  - For a data constructor or data struct the table is only a hash-cons table of values: it is never
 *    scanned, has no indexes and no windows, and its contents are not facts. Interning a data value (in a
 *    head, a comparison or a binding equation) has no observable effect. */
final class Relation(val tag: Int, val sym: RelSym, val arity: Int, indexCols: Set[Vector[Int]]):
  val tuples: mutable.ArrayBuffer[Array[Any]] = mutable.ArrayBuffer.empty
  private val interned = mutable.HashMap.empty[Key, Int]
  private val indexes: Map[Vector[Int], mutable.HashMap[Key, mutable.ArrayBuffer[Int]]] =
    indexCols.map(c => c -> mutable.HashMap.empty[Key, mutable.ArrayBuffer[Int]]).toMap

  /** Whether the tuples are values only (a data constructor or data struct), not facts. */
  val isData: Boolean = sym.isData

  /** The number of tuples. */
  def size: Int = tuples.length

  /** The identity of a tuple; -1 if it was never interned. */
  def lookup(t: Array[Any]): Int = interned.getOrElse(Key(t), -1)

  /** Interns a tuple (for a relation of F: asserts it). Returns its identity. */
  def intern(t: Array[Any]): Int =
    val k = Key(t)
    interned.get(k) match
      case Some(n) => n
      case None =>
        val n = tuples.length
        tuples += t
        interned(k) = n
        for (cols, idx) <- indexes do idx.getOrElseUpdate(Key(cols.map(t(_)).toArray), mutable.ArrayBuffer.empty) += n
        n

  /** Identities of the tuples with the given values in the given columns, ascending. */
  def index(cols: Vector[Int]): mutable.HashMap[Key, mutable.ArrayBuffer[Int]] = indexes(cols)
