package hugin.compiler

import hugin.util.*
import hugin.util.diagnostics.Problem

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

  /** The current text of the program's files, by path. Spans of items parsed from their slices resolve
   *  to the current text through the slices' placement; results memoised from an earlier revision (see
   *  [[ProgramElab]]) may also keep spans into the whole source file they were parsed from (items that do
   *  not parse on their own, the unit's source), at the same positions: the diagnostics are moved to the
   *  current one, so that all spans of a file are in one source file. */
  var sources: Map[String, SourceFile] = Map.empty

  /** A diagnostic with its spans in the current text of its file (see [[sources]]). */
  def placed(d: Diagnostic): Diagnostic =
    if sources.isEmpty then d else d.mapSpans(sp => sources.get(sp.source.path).fold(sp)(sp.in))

  def report(d: Diagnostic): Unit = reporter.report(placed(d))

  /** Reports a problem (see [[Problem.toDiagnostic]]). */
  def report(p: Problem): Unit = report(p.toDiagnostic)

def ctx(using c: Context): Context = c
