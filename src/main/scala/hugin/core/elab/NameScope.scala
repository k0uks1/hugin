package hugin.core
package elab

import scala.collection.immutable.VectorMap
import scala.collection.mutable

/** The top-level names of an elaboration and the globals they denote, in declaration order: a mutable map
 *  (with the order and the update semantics of a `LinkedHashMap`) over a persistent `VectorMap`, so that
 *  a [[copy]] for the elaboration of one item ([[ElabState.fork]]) costs nothing, where copying the names
 *  of a large program for every item cost the program's size each time (issue #60; the persistent
 *  state of Lean 4's elaborator and Agda's `TCState` serve the same purpose).
 *
 *  A [[begin]]…[[rollback]] transaction drops the names added since it began: the names that were not
 *  in scope at its start (an item with an error declares nothing). Names that were in scope stay, with
 *  their current globals. The transaction logs the first write of every name since it began. */
final class NameScope private (private var names: VectorMap[Name, Int]) extends mutable.AbstractMap[Name, Int]:
  def this() = this(VectorMap.empty)

  def get(key: Name): Option[Int] = names.get(key)
  def iterator: Iterator[(Name, Int)] = names.iterator
  override def size: Int = names.size
  override def knownSize: Int = names.size

  /** Increases with every change of the names (for caches of lookups). */
  def version: Long = changes
  private var changes = 0L

  def addOne(elem: (Name, Int)): this.type =
    changes += 1
    log(elem._1)
    names = names.updated(elem._1, elem._2)
    this

  def subtractOne(key: Name): this.type =
    changes += 1
    log(key)
    names = names.removed(key)
    this

  override def clear(): Unit = names.keysIterator.toList.foreach(subtractOne)

  /** An independent copy (sharing the persistent map). */
  def copy(): NameScope = NameScope(names)

  /** The names as an immutable map. */
  def snapshot: VectorMap[Name, Int] = names

  // ------------------------------------------------------------------ transactions

  /** Every write since the oldest open transaction: the name, and whether it was in scope before. */
  private val writes = mutable.ArrayBuffer.empty[(Name, Boolean)]
  private var open = 0

  private def log(n: Name): Unit = if open > 0 then writes += ((n, names.contains(n)))

  /** Begins a transaction; it must end with [[rollback]] or [[commit]], innermost first. */
  def begin(): Int =
    open += 1
    writes.length

  /** Drops the names that were not in scope when the transaction `mark` began, and ends it. */
  def rollback(mark: Int): Unit =
    val firstWrites = mutable.LinkedHashMap.empty[Name, Boolean]
    for (n, before) <- writes.iterator.drop(mark) do firstWrites.getOrElseUpdate(n, before)
    for (n, before) <- firstWrites if !before do names = names.removed(n)
    changes += 1
    commit(mark)

  /** Ends the transaction `mark`, keeping its changes (an enclosing transaction can still drop them). */
  def commit(mark: Int): Unit =
    open -= 1
    if open == 0 then writes.clear()
