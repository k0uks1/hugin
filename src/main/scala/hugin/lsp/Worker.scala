package hugin.lsp

import hugin.query.{Cancelled, Database}
import hugin.util.Cancellation
import java.util.concurrent.{CompletableFuture, LinkedBlockingQueue, ThreadPoolExecutor, TimeUnit}
import java.util.concurrent.atomic.AtomicLong
import org.eclipse.lsp4j.jsonrpc.ResponseErrorException
import org.eclipse.lsp4j.jsonrpc.messages.{ResponseError, ResponseErrorCode}
import scala.util.control.NonFatal

/** Runs the language server's work with the query database off lsp4j's message thread, cancelling work
 *  for a text that changed again, in the style of salsa and rust-analyzer (and Lean's server, which
 *  cancels the snapshots after an edit).
 *
 *  - All database access happens in tasks run by one worker thread, in the order the messages arrived,
 *    and under [[lock]]: the database is single-threaded.
 *  - Every edit (opening, changing or closing a document, files changed on disk) starts a new
 *    *generation*. The message thread only counts it; the edit's task changes the database inputs and
 *    then, if no newer edit has arrived, refreshes (computes and publishes diagnostics) with the
 *    database's cancellation set to "a newer edit arrived". A newer edit therefore stops the refresh at
 *    the next query boundary ([[hugin.query.Cancelled]]; the database keeps no memo of a cancelled query),
 *    and its own task refreshes for the latest text. A burst of edits costs one refresh.
 *  - A refresh publishes through [[Turn.publish]], which sends only while its generation is the latest:
 *    a stale result is never published. Counting a generation and publishing exclude each other.
 *  - Requests are tasks too, so they see every edit received before them. One cancelled by a later edit
 *    (or by the client's `$/cancelRequest`) answers `ContentModified`, as rust-analyzer does.
 */
final class Worker(db: Database):
  private val lock = Object()
  private val generation = AtomicLong()
  private val publishing = Object()
  private val executor = ThreadPoolExecutor(
    0,
    1,
    5,
    TimeUnit.SECONDS,
    LinkedBlockingQueue[Runnable](),
    (r: Runnable) => {
      val t = Thread(r, "hugin-lsp-worker")
      t.setDaemon(true)
      t
    }
  )

  /** The refresh of one generation: what it computes may be published while no newer edit arrived. */
  final class Turn(val generation: Long):
    def current: Boolean = Worker.this.generation.get == generation

    /** Runs `send` if this is still the latest generation (and no edit is counted meanwhile). */
    def publish(send: => Unit): Unit = publishing.synchronized(if current then send)

  /** An edit: `change` sets the database inputs (it is not cancelled), then `refresh` runs unless a newer
   *  edit arrived, and is cancelled when one does. */
  def edit(change: => Unit)(refresh: Turn => Unit): Unit =
    val turn = Turn(publishing.synchronized(generation.incrementAndGet()))
    executor.execute(() =>
      locked {
        change
        if turn.current then dropIfCancelled(() => !turn.current)(refresh(turn))
      }
    )

  /** A task that is neither an edit nor cancellable (a change of settings). */
  def run(body: => Unit): Unit = executor.execute(() => locked(body))

  /** A request: computed after the messages received before it; answers `ContentModified` if an edit
   *  arrives or the client cancels it before it is done. */
  def request[T](compute: => T): CompletableFuture[T] =
    val future = CompletableFuture[T]()
    val since = generation.get
    executor.execute(() =>
      if !future.isDone then
        locked {
          try future.complete(cancellable(() => generation.get != since || future.isCancelled)(compute))
          catch
            case _: Cancelled =>
              future.completeExceptionally(ResponseErrorException(ResponseError(
                ResponseErrorCode.ContentModified,
                "content modified",
                null
              )))
            case NonFatal(e) => future.completeExceptionally(e)
        }
    )
    future

  /** Completed when the work submitted so far is done (for tests and benchmarks). */
  def idle(): CompletableFuture[Unit] =
    val done = CompletableFuture[Unit]()
    executor.execute(() => done.complete(()))
    done

  /** Runs `body` with the database, excluding the worker (for tests: the worker's tasks wait meanwhile). */
  def withDatabase[T](body: => T): T = lock.synchronized(body)

  private def locked(body: => Unit): Unit =
    lock.synchronized {
      try body
      catch case NonFatal(e) => System.err.println(s"hugin lsp: ${e.getClass.getName}: ${e.getMessage}")
    }

  /** Runs `body` with the database's cancellation set to `cancelled`; a cancelled body is dropped (for an
   *  edit: the newer edit refreshes) or rethrown (for a request, which answers it). */
  private def cancellable[T](cancelled: Cancellation)(body: => T): T =
    db.cancellation = cancelled
    try body
    finally db.cancellation = Database.neverCancelled

  private def dropIfCancelled(cancelled: Cancellation)(body: => Unit): Unit =
    try cancellable[Unit](cancelled)(body)
    catch case _: Cancelled => ()
