package hugin.platform

import hugin.util.{Cancellation, SourceFiles}
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}

/** The JVM implementations of the compiler's platform interfaces. This package is the platform-specific
 *  part of the compiler (with `cli`, `repl` and `lsp`): another platform provides its own `Platform`. */
object Platform:
  /** The file system and the class path. */
  val files: SourceFiles = JvmSourceFiles

  /** The interrupt of the current thread (`Thread.interrupted`, which also clears it). */
  val cancellation: Cancellation = () => Thread.interrupted()

/** Files through `java.nio.file`, resources from the class path. An invalid path is reported by
 *  `java.nio.file.InvalidPathException`, an `IllegalArgumentException`. */
private object JvmSourceFiles extends SourceFiles:
  def readFile(path: String): Option[String] =
    try
      val p = Path.of(path)
      if Files.isRegularFile(p) then Some(Files.readString(p)) else None
    catch case _: java.nio.file.InvalidPathException => None

  def readResource(name: String): Option[String] =
    Option(getClass.getResourceAsStream(name)).map { in =>
      try String(in.readAllBytes(), UTF_8)
      finally in.close()
    }

  def normalize(path: String): String = Path.of(path).normalize.toString

  def fileName(path: String): Option[String] = Option(Path.of(path).getFileName).map(_.toString)

  def resolveSibling(from: String, path: String): String =
    Option(Path.of(from).getParent).map(_.resolve(path)).getOrElse(Path.of(path)).normalize.toString
