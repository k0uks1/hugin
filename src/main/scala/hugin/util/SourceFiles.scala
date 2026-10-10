package hugin.util

/** Where the compiler reads files and the resources bundled with it (the standard library, the error
 *  explanations, the reference's URL), and the path arithmetic of imports. The compiler's packages use
 *  it through [[hugin.platform.Platform.files]], so that they do not depend on the platform's file API;
 *  the JVM's implementation reads the file system and the class path. */
trait SourceFiles:
  /** The text of the regular file at `path`, or `None` if there is none or `path` is not a valid path. */
  def readFile(path: String): Option[String]

  /** The text (UTF-8) of the bundled resource `name` (an absolute resource name, `/hugin/...`), if any. */
  def readResource(name: String): Option[String]

  /** The path without redundant parts (`.`, `dir/..`), with the platform's separators. Throws an
   *  `IllegalArgumentException` if `path` is not a valid path; so do the other path operations. */
  def normalize(path: String): String

  /** The last part of the path, if it has one (a root has none). */
  def fileName(path: String): Option[String]

  /** `path` resolved against the directory of the file `from` (against the current directory if `from`
   *  has none), normalized. */
  def resolveSibling(from: String, path: String): String

/** A check, made at points where stopping is safe, whether the work in progress is no longer wanted: an
 *  evaluation's fixpoint loop asks it once per round and ends with an `InterruptedException` if so. */
trait Cancellation:
  /** Whether the work has been cancelled. A cancellation is reported once: asking again after it was
   *  reported may answer `false`. */
  def cancelled(): Boolean
