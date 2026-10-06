package hugin.query

import scala.collection.mutable

/** An input of the database: a value set from outside (e.g. the text of a file), keyed by `K`. */
abstract class Input[K, V](val name: String):
  override def toString: String = name

/** A derived query: a pure function of other queries and inputs, memoised by the database. `compute` must
 *  read everything it depends on through the given [[Database]], so that dependencies are recorded. */
abstract class Query[K, V](val name: String):
  def compute(key: K)(using db: Database): V
  override def toString: String = name

/** A cycle among queries: `path` lists the active queries from the outermost to the re-entered one. */
final class CycleError(val path: List[String]) extends RuntimeException(s"cycle in queries: ${path.mkString(" -> ")}")

/** Thrown when a query reads an input that was never set. */
final class MissingInput(val description: String) extends RuntimeException(s"input not set: $description")

/** A demand-driven, incremental computation database in the style of rustc's query system and salsa.
 *
 *  - Inputs are set with [[set]]; changing an input to a different value starts a new revision.
 *  - Queries are computed on demand ([[apply]]) and memoised together with the inputs and queries they read.
 *  - In a later revision a memoised result is reused if none of its dependencies changed since it was
 *    last verified ("red-green" revalidation, checking dependencies recursively and recomputing them first).
 *  - Early cut-off: a recomputed result equal to the previous one does not count as a change, so
 *    dependents are not recomputed.
 *
 *  Results must be immutable values with meaningful `equals` for early cut-off to apply. The database is
 *  single-threaded.
 */
final class Database:
  private type Slot = (AnyRef, Any)

  private final class InputCell(val value: Any, val changedAt: Long)
  private final class Memo(var value: Any, var verifiedAt: Long, var changedAt: Long, var deps: Vector[Slot])
  private final class Frame(val slot: Slot, val deps: mutable.LinkedHashSet[Slot])

  private var current: Long = 0
  private val inputs = mutable.HashMap.empty[Slot, InputCell]
  private val memos = mutable.HashMap.empty[Slot, Memo]
  private val stack = mutable.ArrayBuffer.empty[Frame]

  /** Counters for tests and diagnostics of incrementality. */
  object stats:
    /** Number of query executions. */
    var computed = 0

    /** Number of memoised results reused after verification in a later revision. */
    var reused = 0

    /** Executions per query name. */
    val computedBy: mutable.Map[String, Int] = mutable.HashMap.empty.withDefaultValue(0)
    def reset(): Unit =
      computed = 0
      reused = 0
      computedBy.clear()

  /** The current revision; it increases whenever an input changes. */
  def revision: Long = current

  /** Sets an input. Setting an equal value does not start a new revision. */
  def set[K, V](input: Input[K, V], key: K, value: V): Unit =
    require(stack.isEmpty, "inputs cannot be changed while queries are running")
    val slot = (input, key)
    inputs.get(slot) match
      case Some(cell) if cell.value == value =>
      case _ =>
        current += 1
        inputs(slot) = InputCell(value, current)

  /** Removes an input (e.g. a closed file); dependents are recomputed on their next use. */
  def remove[K, V](input: Input[K, V], key: K): Unit =
    if inputs.remove((input, key)).isDefined then current += 1

  /** Reads an input, recording the dependency of the running query. */
  def get[K, V](input: Input[K, V], key: K): V =
    val slot = (input, key)
    record(slot)
    inputs.get(slot) match
      case Some(cell) => cell.value.asInstanceOf[V]
      case None => throw MissingInput(s"$input($key)")

  /** Whether an input is set (also recorded as a dependency). */
  def has[K, V](input: Input[K, V], key: K): Boolean =
    record((input, key))
    inputs.contains((input, key))

  /** Demands a query, recording the dependency of the running query. */
  def apply[K, V](query: Query[K, V], key: K): V =
    val slot = (query, key)
    record(slot)
    fresh(slot).value.asInstanceOf[V]

  private def record(slot: Slot): Unit = stack.lastOption.foreach(_.deps += slot)

  /** Brings the memo of a query up to date with the current revision and returns it. */
  private def fresh(slot: Slot): Memo =
    if stack.exists(_.slot == slot) then
      val path = stack.dropWhile(_.slot != slot).map(f => describe(f.slot)).toList :+ describe(slot)
      throw CycleError(path)
    memos.get(slot) match
      case Some(m) if m.verifiedAt == current => m
      case Some(m) if m.deps.forall(d => changedAt(d) <= m.verifiedAt) =>
        m.verifiedAt = current
        stats.reused += 1
        m
      case old => execute(slot, old)

  /** The revision in which a dependency last changed, after bringing it up to date. */
  private def changedAt(slot: Slot): Long = slot._1 match
    case _: Input[?, ?] => inputs.get(slot).map(_.changedAt).getOrElse(current)
    case _ => fresh(slot).changedAt

  private def execute(slot: Slot, old: Option[Memo]): Memo =
    val (query, key) = slot.asInstanceOf[(Query[Any, Any], Any)]
    val frame = Frame(slot, mutable.LinkedHashSet.empty)
    stack += frame
    val value =
      try query.compute(key)(using this)
      finally stack.remove(stack.length - 1)
    stats.computed += 1
    stats.computedBy(query.name) += 1
    val memo = old match
      case Some(m) if m.value == value =>
        // early cut-off: same value, dependents need not be recomputed
        Memo(m.value, current, m.changedAt, frame.deps.toVector)
      case _ => Memo(value, current, current, frame.deps.toVector)
    memos(slot) = memo
    memo

  private def describe(slot: Slot): String = s"${slot._1}(${slot._2})"
