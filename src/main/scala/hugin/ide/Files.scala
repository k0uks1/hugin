package hugin.ide

import hugin.compiler.SourceLoader
import hugin.query.{CompileKey, Database, FileDiagnostics, Parse}
import hugin.util.{Diagnostic, Severity, SourceFile}
import hugin.util.diagnostics.{Code, LintLevels}
import scala.util.control.NonFatal

/** The editor features of Hugin, independent of a protocol (issues #147 and #132, `docs/design/web-ide.md`):
 *  what hover shows, where a name is declared, which completions fit, which fixes apply, how the outline
 *  nests. Shared by the language server (`hugin.lsp`, which only encodes the answers in the protocol's
 *  terms), the browser build and the CLI.
 *
 *  Every feature takes the compilation of a program file (a [[hugin.query.CompileKey]]) and offsets into
 *  its text, and answers with plain case classes and [[hugin.util.Span]]s. Offsets index UTF-16 code
 *  units, as JVM strings, JavaScript strings and CodeMirror positions do. Programs (`.hgn`) get every
 *  feature, facts files (`.facts`) only their syntax diagnostics. */
object Files:
  /** Whether a file is a facts file (ground facts for input relations), not a program. */
  def isFacts(path: String): Boolean = path.endsWith(".facts")

  /** Whether a file belongs to the bundled standard library (it has no location an editor could open). */
  def isLibrary(path: String): Boolean = path.startsWith(SourceLoader.StdlibPrefix)

  /** The module of a file of the bundled standard library: `prelude`, `std/graph`. */
  def libraryModule(path: String): String = path.stripPrefix(SourceLoader.StdlibPrefix).stripSuffix(".hgn")

  private[ide] def source(path: String)(using db: Database): SourceFile = db(Parse, path).source

/** The diagnostics of a compilation, by file. */
object Diagnostics:
  /** The compiler's diagnostics for a program by file ([[hugin.query.FileDiagnostics]]): its own and those
   *  in the files it imports; for a facts file, its syntax diagnostics. A compiler crash becomes an error
   *  diagnostic of the file (E1102), so that it does not take other files' diagnostics with it. */
  def of(key: CompileKey)(using db: Database): List[FileDiagnostics] =
    val path = key.path
    try
      if Files.isFacts(path) then List(FileDiagnostics(path, db(Parse, path).diagnostics)).filter(_.diagnostics.nonEmpty)
      // editors have no lint flags: the lints that are off by default are not shown
      else
        FileDiagnostics.of(key).map(f => f.copy(diagnostics = f.diagnostics.filter(LintLevels.onByDefault))).filter(_.diagnostics.nonEmpty)
    catch
      case NonFatal(e) =>
        val crash = Diagnostic(Severity.Error, Code.E1102, s"internal compiler error: $e", notes = List("please report this as a bug"))
        List(FileDiagnostics(path, List(crash)))

  /** All diagnostics of a compilation, including those in the files it imports. */
  def all(key: CompileKey)(using Database): List[Diagnostic] = of(key).flatMap(_.diagnostics)
