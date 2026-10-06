package hugin.compiler

import hugin.util.*

/** The state threaded through all phases: the unit, the settings, the diagnostics reporter, and where
 *  imported files and their elaborations come from. */
final class Context(
    val unit: CompilationUnit,
    val settings: Settings,
    val reporter: Reporter,
    val libraries: Libraries = Libraries.direct(SourceLoader.files)
):
  /** Wall-clock time per phase that ran, in nanoseconds, in phase order (for `--stats`). */
  val timings: scala.collection.mutable.ListBuffer[(String, Long)] = scala.collection.mutable.ListBuffer.empty

  /** The current text of the program's files, by path. Results memoised from an earlier revision (see
   *  [[ProgramElab]]) keep spans into the source file they were parsed from, at the same positions; the
   *  diagnostics are moved to the current one, so that all spans of a file are in one source file. */
  var sources: Map[String, SourceFile] = Map.empty

  def report(d: Diagnostic): Unit =
    reporter.report(if sources.isEmpty then d else d.mapSpans(sp => sources.get(sp.source.path).fold(sp)(f => sp.copy(source = f))))
  def error(code: String, msg: String, span: Span, label: String = ""): Unit =
    report(Diagnostic.error(code, msg, span, label))

def ctx(using c: Context): Context = c
