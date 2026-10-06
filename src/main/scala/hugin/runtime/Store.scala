package hugin.runtime

import hugin.obj.RelSym
import scala.collection.mutable

/** A tuple key with structural equality. */
final class Key(val ws: Array[Any]):
  override def hashCode: Int = java.util.Arrays.hashCode(ws.asInstanceOf[Array[AnyRef]])
  override def equals(o: Any): Boolean = o match
    case k: Key => java.util.Arrays.equals(ws.asInstanceOf[Array[AnyRef]], k.ws.asInstanceOf[Array[AnyRef]])
    case _ => false

/** Facts of one relation: tuples indexed by n, the interning map, and hash indexes on bound columns (Section 9.4). */
final class Relation(val tag: Int, val sym: RelSym, val arity: Int, indexCols: Set[Vector[Int]]):
  val tuples: mutable.ArrayBuffer[Array[Any]] = mutable.ArrayBuffer.empty
  private val interned = mutable.HashMap.empty[Key, Int]
  private val indexes: Map[Vector[Int], mutable.HashMap[Key, mutable.ArrayBuffer[Int]]] =
    indexCols.map(c => c -> mutable.HashMap.empty[Key, mutable.ArrayBuffer[Int]]).toMap

  def size: Int = tuples.length
  def lookup(t: Array[Any]): Int = interned.getOrElse(Key(t), -1)

  /** Interns a tuple; returns (n, isNew). */
  def intern(t: Array[Any]): (Int, Boolean) =
    val k = Key(t)
    interned.get(k) match
      case Some(n) => (n, false)
      case None =>
        val n = tuples.length
        tuples += t
        interned(k) = n
        for (cols, idx) <- indexes do
          idx.getOrElseUpdate(Key(cols.map(t(_)).toArray), mutable.ArrayBuffer.empty) += n
        (n, true)

  def index(cols: Vector[Int]): mutable.HashMap[Key, mutable.ArrayBuffer[Int]] = indexes(cols)
