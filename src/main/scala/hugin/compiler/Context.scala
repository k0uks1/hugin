package hugin.compiler

import hugin.util.*

/** The state threaded through all phases: the unit, the settings, the diagnostics reporter, and where
 *  imported files come from. */
final class Context(
    val unit: CompilationUnit,
    val settings: Settings,
    val reporter: Reporter,
    val loader: SourceLoader = SourceLoader.files
):
  /** Wall-clock time per phase that ran, in nanoseconds, in phase order (for `--stats`). */
  val timings: scala.collection.mutable.ListBuffer[(String, Long)] = scala.collection.mutable.ListBuffer.empty

  def report(d: Diagnostic): Unit =
    reporter.report(d)
  def error(code: String, msg: String, span: Span, label: String = ""): Unit =
    report(Diagnostic.error(code, msg, span, label))

def ctx(using c: Context): Context = c
