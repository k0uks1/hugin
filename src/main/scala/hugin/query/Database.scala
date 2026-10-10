package hugin.query

import hugin.util.Cancellation
import scala.collection.mutable

/** An input of the database: a value set from outside (e.g. the text of a file), keyed by `K`. */
abstract class Input[K, V](val name: String):
  /** The value of an input that was never set, read on first use (e.g. a file from disk). A default stays
   *  in place until the input is set or removed. */
  def default(key: K): Option[V] = None
  override def toString: String = name

/** A derived query: a pure function of other queries and inputs, memoised by the database. `compute` must
 *  read everything it depends on through the given [[Database]], so that dependencies are recorded. */
abstract class Query[K, V](val name: String):
  def compute(key: K)(using db: Database): V

  /** The value of a query that is demanded again while it is being computed. `None` (the default) makes
   *  such a cycle an error ([[CycleError]]); a value lets the outer computation continue with it (e.g. an
   *  empty declaration while its own declaration is elaborated). The fallback is not memoised; the queries
   *  that received it can ask [[Database.recoveredFromCycle]] and report the cycle themselves. */
  def onCycle(key: K): Option[V] = None
  override def toString: String = name

/** A side output of queries, collected along the dependencies (e.g. diagnostics). Pushed values belong to
 *  the running query: they are replaced when it is recomputed, also when its value stays the same (early
 *  cut-off), and reused with it otherwise. */
abstract class Accumulator[A](val name: String):
  override def toString: String = name

/** A cycle among queries: `path` lists the active queries from the outermost to the re-entered one. */
final class CycleError(val path: List[String]) extends RuntimeException(s"cycle in queries: ${path.mkString(" -> ")}")

/** Thrown when a query is demanded after the computation was cancelled ([[Database.cancellation]]). It
 *  unwinds every query being computed, none of which stores a memo, and is not caught by handlers of
 *  non-fatal exceptions (it is a control throwable), so a compiler's error recovery does not swallow it. */
final class Cancelled extends scala.util.control.ControlThrowable("query computation cancelled")

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
 *  - Eviction ([[collect]]): memos that no recent demand can reach are dropped, so that the memory a
 *    long-running client (an editor, a REPL session) holds stays proportional to what it currently
 *    asks, not to its history of edits. A demand from outside any query (a *root*) is recorded with the
 *    epoch it was made in; an epoch is a revision in which queries were demanded. A collection keeps the
 *    memos reachable, along their recorded dependencies, from the roots demanded in the last
 *    `retainEpochs` epochs and from the memos verified in them, and drops the others (results of keys
 *    that no longer exist, such as the items and slices of an earlier text, or of programs no longer
 *    asked about). Collections run automatically when an epoch starts and the number of memos has grown
 *    past `collectAbove` and twice the number kept by the previous collection, so their cost is
 *    amortised. Dropping a memo is always safe: a dropped result is computed again when demanded, and
 *    every memo kept keeps its dependencies.
 *
 *  - Cancellation ([[cancellation]]): a client can stop a computation it no longer needs (an editor whose
 *    text changed again). The check is asked whenever a query is demanded, and between the phases of a
 *    compilation; if it answers yes, [[Cancelled]] unwinds the running queries. A query that is unwound
 *    stores no memo (its earlier memo, if any, stays as it was and is verified again on its next demand),
 *    and the memos completed before the check are complete results, so the database stays consistent.
 *    The check is a [[hugin.util.Cancellation]] the client injects, not a thread interrupt, so that it
 *    works on any platform.
 *
 *  Results must be immutable values with meaningful `equals` for early cut-off to apply. The database is
 *  single-threaded: a client using it from several threads makes them take turns (the language server
 *  runs its work on one worker thread under a lock); only [[cancellation]] is asked from the computing
 *  thread about state another thread may change.
 */
final class Database(val retainEpochs: Int = 2, val collectAbove: Int = 1024):
  private type Slot = (AnyRef, Any)

  private final class InputCell(val value: Any, val changedAt: Long)
  private final class Memo(
      var value: Any,
      var verifiedAt: Long,
      var changedAt: Long,
      var deps: Vector[Slot],
      val accumulated: Map[Accumulator[?], Vector[Any]]
  )
  private final class Frame(val slot: Slot, val deps: mutable.LinkedHashSet[Slot]):
    val accumulated: mutable.LinkedHashMap[Accumulator[?], mutable.ArrayBuffer[Any]] = mutable.LinkedHashMap.empty

    /** Computed with a cycle fallback (passed on to the demanding query, up to the cycle's head). */
    var recovered = false

    /** Re-entered by a cycle that was recovered: this query closed the cycle (not passed on). */
    var cycleHead = false

  private var current: Long = 0
  private val inputs = mutable.HashMap.empty[Slot, InputCell]
  private val memos = mutable.HashMap.empty[Slot, Memo]
  private val stack = mutable.ArrayBuffer.empty[Frame]

  /** The queries demanded from outside any query, with the epoch of their last demand. */
  private val roots = mutable.HashMap.empty[Slot, Long]

  /** The current epoch (see [[collect]]) and the revision it started in. */
  private var epoch = 0L
  private val epochStarts = mutable.ArrayDeque.empty[Long]

  /** The number of memos kept by the last collection. */
  private var kept = 0

  /** Counters for tests and diagnostics of incrementality. */
  object stats:
    /** Number of query executions. */
    var computed = 0

    /** Number of memoised results reused after verification in a later revision. */
    var reused = 0

    /** Executions per query name. */
    val computedBy: mutable.Map[String, Int] = mutable.HashMap.empty.withDefaultValue(0)

    /** Number of memos dropped by collections. */
    var evicted = 0

    /** Number of collections. */
    var collections = 0

    def reset(): Unit =
      computed = 0
      reused = 0
      evicted = 0
      collections = 0
      computedBy.clear()

  /** Whether the computation in progress is no longer wanted: asked whenever a query is demanded (see
   *  [[checkCancelled]]). Set by the client around a computation; by default, never (not the platform's
   *  thread interrupt: the database is shared by the computations of a client). Unlike the evaluation
   *  engine's, a database cancellation must keep answering yes until the client resets it, since every
   *  query being unwound asks it again. */
  @volatile var cancellation: Cancellation = Database.neverCancelled

  /** Throws [[Cancelled]] if the computation in progress was cancelled. */
  def checkCancelled(): Unit = if cancellation.cancelled() then throw Cancelled()

  /** The current revision; it increases whenever an input changes. */
  def revision: Long = current

  /** The number of memoised query results. */
  def memoCount: Int = memos.size

  /** The number of memoised results of one query. */
  def memoCount(query: Query[?, ?]): Int = memos.keysIterator.count(_._1 eq query)

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
    if inputs.remove((input, key)).isDefined then
      current += 1
      removedAt((input, key)) = current

  /** Reads an input, recording the dependency of the running query. */
  def get[K, V](input: Input[K, V], key: K): V =
    val slot = (input, key)
    record(slot)
    cell(input, key) match
      case Some(c) => c.value.asInstanceOf[V]
      case None => throw MissingInput(s"$input($key)")

  /** Whether an input is set or has a default (also recorded as a dependency). */
  def has[K, V](input: Input[K, V], key: K): Boolean =
    record((input, key))
    cell(input, key).isDefined

  /** The revision in which an input was last removed: its default, read again, dates from then. */
  private val removedAt = mutable.HashMap.empty[Slot, Long]

  /** The cell of an input, filled from its default on first use. A default does not start a revision:
   *  the value is treated as if it had been there all along, or since the input was removed (so that the
   *  results computed from the value before the removal are not taken as still valid). */
  private def cell[K, V](input: Input[K, V], key: K): Option[InputCell] =
    val slot = (input, key)
    inputs.get(slot).orElse {
      input.default(key).map { v =>
        val c = InputCell(v, removedAt.getOrElse(slot, 0L))
        inputs(slot) = c
        c
      }
    }

  /** Demands a query, recording the dependency of the running query. */
  def apply[K, V](query: Query[K, V], key: K): V =
    checkCancelled()
    val slot = (query, key)
    record(slot)
    if stack.isEmpty then demanded(slot)
    fresh(slot).value.asInstanceOf[V]

  /** Demands a query without recording a dependency of the running query: the caller must record, with
   *  tracked reads, dependencies that cover everything it uses of the value (e.g. per-declaration
   *  projections of a shared result), so that it is recomputed whenever what it used changed. */
  def untracked[K, V](query: Query[K, V], key: K): V =
    checkCancelled()
    if stack.isEmpty then demanded((query, key))
    fresh((query, key)).value.asInstanceOf[V]

  /** Records a demand from outside any query; the first one in a revision starts an epoch, which may
   *  collect first (see [[collect]]). */
  private def demanded(slot: Slot): Unit =
    if epochStarts.lastOption.forall(_ != current) then
      if memos.size > collectAbove && memos.size > 2 * kept then collect()
      epoch += 1
      epochStarts += current
      while epochStarts.length > retainEpochs.max(1) do epochStarts.removeHead()
    roots(slot) = epoch

  /** Drops the memos that are not reachable, along recorded dependencies, from the roots demanded in the
   *  last `retainEpochs` epochs (the current one included, if it started) or from the memos verified in
   *  them; forgets older roots. Returns the number of memos dropped. Must not be called from a query. */
  def collect(): Int =
    require(stack.isEmpty, "memos cannot be collected while queries are running")
    val since = epoch - retainEpochs.max(1) + 1
    roots.filterInPlace((_, e) => e >= since)
    val oldest = epochStarts.headOption.getOrElse(current)
    val live = mutable.HashSet.empty[Slot]
    val todo = mutable.ArrayBuffer.empty[Slot]
    def mark(slot: Slot): Unit = if memos.contains(slot) && live.add(slot) then todo += slot
    roots.keysIterator.foreach(mark)
    for (slot, m) <- memos if m.verifiedAt >= oldest do mark(slot)
    while todo.nonEmpty do memos(todo.remove(todo.length - 1)).deps.foreach(mark)
    val before = memos.size
    memos.filterInPlace((slot, _) => live(slot))
    kept = memos.size
    stats.collections += 1
    stats.evicted += before - kept
    before - kept

  private def record(slot: Slot): Unit = stack.lastOption.foreach(_.deps += slot)

  /** Adds a value to an accumulator on behalf of the running query (ignored outside queries). */
  def push[A](acc: Accumulator[A], value: A): Unit =
    stack.lastOption.foreach(_.accumulated.getOrElseUpdate(acc, mutable.ArrayBuffer.empty) += value)

  /** The values pushed to `acc` by a query and, transitively, by every query it depends on, each query
   *  once, dependencies before dependents. Brings the query up to date first. */
  def accumulated[K, V, A](acc: Accumulator[A], query: Query[K, V], key: K): Vector[A] =
    apply(query, key)
    val seen = mutable.HashSet.empty[Slot]
    val out = mutable.ArrayBuffer.empty[A]
    def visit(slot: Slot): Unit =
      if seen.add(slot) then
        memos.get(slot).foreach { m =>
          m.deps.foreach(visit)
          m.accumulated.get(acc).foreach(vs => out ++= vs.asInstanceOf[Vector[A]])
        }
    visit((query, key))
    out.toVector

  /** The values pushed to `acc` by a query itself (not by the queries it depends on), in order. Brings the
   *  query up to date first. */
  def pushed[K, V, A](acc: Accumulator[A], query: Query[K, V], key: K): Vector[A] =
    apply(query, key)
    memos.get((query, key)).flatMap(_.accumulated.get(acc)).fold(Vector.empty)(_.asInstanceOf[Vector[A]])

  /** Whether the running query received a cycle fallback ([[Query.onCycle]]), directly or through a query
   *  it demanded during this computation. */
  def recoveredFromCycle: Boolean = stack.lastOption.exists(f => f.recovered || f.cycleHead)

  /** Brings the memo of a query up to date with the current revision and returns it. */
  private def fresh(slot: Slot): Memo =
    if stack.exists(_.slot == slot) then
      val (query, key) = slot.asInstanceOf[(Query[Any, Any], Any)]
      query.onCycle(key) match
        case Some(fallback) =>
          // the queries inside the cycle computed with the fallback; the re-entered one closes it
          val cycle = stack.dropWhile(_.slot != slot)
          cycle.head.cycleHead = true
          cycle.tail.foreach(_.recovered = true)
          return Memo(fallback, current, current, Vector.empty, Map.empty)
        case None =>
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
    // a query that computed with a fallback passes the recovery on to the query that demanded it
    if frame.recovered && !frame.cycleHead then stack.lastOption.foreach(_.recovered = true)
    val accumulated = frame.accumulated.view.mapValues(_.toVector).toMap
    stats.computed += 1
    stats.computedBy(query.name) += 1
    val memo = old match
      case Some(m) if m.value == value =>
        // early cut-off: same value, dependents need not be recomputed (side outputs are the new ones)
        Memo(m.value, current, m.changedAt, frame.deps.toVector, accumulated)
      case _ => Memo(value, current, current, frame.deps.toVector, accumulated)
    memos(slot) = memo
    memo

  private def describe(slot: Slot): String = s"${slot._1}(${slot._2})"

object Database:
  val neverCancelled: Cancellation = () => false
