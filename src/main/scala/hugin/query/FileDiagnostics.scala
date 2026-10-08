package hugin.query

import hugin.util.*

/** The diagnostics of one file of a compilation, in the order the compiler reports them. */
final case class FileDiagnostics(path: String, diagnostics: List[Diagnostic])

/** The diagnostics of a compilation by file: the program's files and each library it includes, in the
 *  order of their paths, each with its diagnostics in the order of the compiler's output; concatenated,
 *  they are the compilation's output ([[Compiled.diagnostics]]). */
object FileDiagnostics:
  /** The diagnostics of the compilation `key` by file. */
  def of(key: CompileKey)(using db: Database): List[FileDiagnostics] =
    val sorted = db(Compile, key).diagnostics
    val paths = sorted.map(_.primarySpan.source.path).distinct
    val byPath = sorted.groupBy(_.primarySpan.source.path)
    paths.map(p => FileDiagnostics(p, byPath(p)))

  /** The diagnostics of the compilation `key` in the file `path` (none if it has none). */
  def in(key: CompileKey, path: String)(using db: Database): List[Diagnostic] =
    of(key).find(_.path == path).fold(Nil)(_.diagnostics)
