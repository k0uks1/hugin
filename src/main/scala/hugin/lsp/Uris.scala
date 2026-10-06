package hugin.lsp

import hugin.compiler.SourceLoader
import java.net.URI
import java.nio.file.Path
import scala.util.Try

/** Conversion between document URIs and the paths that key files in the query database.
 *
 *  A `file:` URI becomes its file system path, so that imports resolve relative to it and unopened
 *  imported files are read from disk by the compiler. Any other URI (an unsaved `untitled:` buffer) is used
 *  as the path unchanged; such a document cannot import files relative to itself.
 */
object Uris:
  /** The database path of a document URI. */
  def path(uri: String): String =
    Try(URI(uri)).toOption
      .filter(u => u.getScheme == "file")
      .flatMap(u => Try(Path.of(u).toString).toOption)
      .getOrElse(uri)

  /** The URI of a database path; `None` for the bundled standard library (`<stdlib>/...`), which has no
   *  location a client could open. */
  def uri(path: String): Option[String] =
    if path.startsWith(SourceLoader.StdlibPrefix) then None
    else if hasScheme(path) then Some(path)
    else Try(Path.of(path).toAbsolutePath.normalize.toUri.toString).toOption

  /** Whether a path is in fact a URI (`untitled:Untitled-1`); a one-letter scheme is a Windows drive. */
  private def hasScheme(s: String): Boolean = "^[A-Za-z][A-Za-z0-9+.-]+:".r.findPrefixOf(s).isDefined
