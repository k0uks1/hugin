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

  /** The current text of the program's files, by path. Spans of items parsed from their slices resolve
   *  to the current text through the slices' placement; results memoised from an earlier revision (see
   *  [[ProgramElab]]) may also keep spans into the whole source file they were parsed from (items that do
   *  not parse on their own, the unit's source), at the same positions: the diagnostics are moved to the
   *  current one, so that all spans of a file are in one source file. */
  var sources: Map[String, SourceFile] = Map.empty

  /** What was reported, in order: each diagnostic a phase reported itself, and each group of diagnostics
   *  of a part of the elaboration (a library's or the program's naming and elaboration), which clients of
   *  the query database read from the parts' accumulators (`hugin.query.FileDiagnostics`). */
  val reported: scala.collection.mutable.ListBuffer[Reported] = scala.collection.mutable.ListBuffer.empty

  /** A diagnostic with its spans in the current text of its file (see [[sources]]). */
  def placed(d: Diagnostic): Diagnostic =
    if sources.isEmpty then d else d.mapSpans(sp => sources.get(sp.source.path).fold(sp)(sp.in))

  def report(d: Diagnostic): Unit =
    reported += Reported.Own(d)
    reporter.report(placed(d))

  /** Reports the diagnostics of a part of the elaboration. */
  def reportPart(part: DiagnosticPart, diagnostics: List[Diagnostic]): Unit =
    reported += Reported.Part(part)
    diagnostics.foreach(d => reporter.report(placed(d)))
  def error(code: String, msg: String, span: Span, label: String = ""): Unit =
    report(Diagnostic.error(code, msg, span, label))

def ctx(using c: Context): Context = c

/** A part of the elaboration whose diagnostics a compilation reports as a group: the naming or the
 *  elaboration of a library, or of the program's top level. */
enum DiagnosticPart:
  case LibraryNames(key: NameKey)
  case LibraryElab(key: LibraryKey)
  case ProgramNames(root: String, prelude: Boolean)
  case ProgramElab(root: String, prelude: Boolean)

/** An entry of [[Context.reported]]. */
enum Reported:
  case Own(diagnostic: Diagnostic)
  case Part(part: DiagnosticPart)
