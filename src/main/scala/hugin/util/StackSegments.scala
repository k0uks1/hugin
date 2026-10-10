package hugin.util

import java.util.concurrent.FutureTask

/** Segmented stacks for recursions whose depth is that of the input (issue #129). The evaluator is a
 *  recursive NbE evaluator: a meta function recursing over a list of n elements nests n levels of
 *  `eval` -> `app` -> `reduceFunction` -> `runTree` -> `eval` (~17 JVM frames per level). On a thread
 *  with the JVM's default 1 MiB stack that overflowed from a few hundred levels, at a depth that varied
 *  between runs with how much of the evaluator the JIT had compiled (an interpreted frame is several
 *  times larger than a compiled one, and inlining merges frames).
 *
 *  A recursion that calls [[deeper]] once per level runs every [[levels]]-th level on a fresh thread
 *  with a stack of [[segmentBytes]], the calling thread blocked until it returns. The stack any one
 *  thread spends on the recursion is then bounded by [[levels]] levels, whatever the depth of the
 *  recursion and whatever stack the caller was given (the 1 MiB of a bench harness or a test thread, the
 *  launcher's 64 MiB): the depth is bounded by memory instead. One thread runs at a time; `start` and
 *  `get` order every write of a segment before what follows, so the evaluator's (unsynchronised) state
 *  is shared safely. */
object StackSegments:
  /** Levels of a recursion run on one stack segment: at the measured worst (~1.5 KiB per level of a
   *  meta function's recursion, interpreted) 64 levels take ~100 KiB of the caller's stack. */
  val levels = 64

  /** The stack of a new segment: room for [[levels]] levels and for the recursions within one level
   *  (deep terms, read-back), which are bounded by the size of a value rather than the depth here. */
  val segmentBytes: Long = 16L << 20

  /** `body`, at recursion depth `depth` (1 for the outermost level): on the current stack, or, every
   *  [[levels]] levels, on a new segment. Exceptions (a [[StackOverflowError]] included) are rethrown
   *  on the calling thread. */
  inline def deeper[A <: AnyRef](depth: Int)(inline body: => A): A =
    if depth % levels != 0 then body else onNewSegment(() => body)

  def onNewSegment[A <: AnyRef](body: () => A): A =
    val task = FutureTask[A](() => body())
    val thread = Thread(null, task, "hugin-stack-segment", segmentBytes)
    thread.setDaemon(true)
    thread.start()
    var interrupted = false
    var result: A | Null = null
    var done = false
    while !done do
      try
        result = task.get()
        done = true
      catch
        case _: InterruptedException =>
          // passed on to the segment (code that polls for cancellation sees it there), and restored here
          interrupted = true
          thread.interrupt()
        case e: java.util.concurrent.ExecutionException =>
          if interrupted then Thread.currentThread().interrupt()
          throw e.getCause
    if interrupted then Thread.currentThread().interrupt()
    result.asInstanceOf[A]
