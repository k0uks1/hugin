package hugin.util.diagnostics

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** Ties the registry to the tests and the sources: every active code has a negative golden test, retired
 *  codes are never reported, codes are never spelled as strings, and every diagnostic is a typed problem. */
class DiagnosticsCoverageSuite extends munit.FunSuite:
  private def files(dir: String, ext: String): List[Path] =
    Files.walk(Path.of(dir)).iterator.asScala.filter(_.toString.endsWith(ext)).toList.sortBy(_.toString)

  /** The codes reported in the rendered diagnostics of the negative golden tests. */
  private lazy val reportedInGoldens: Set[String] =
    val pattern = "(?:error|warning)\\[([EW]\\d{4})\\]".r
    files("tests/neg", ".check").flatMap(p => pattern.findAllMatchIn(Files.readString(p)).map(_.group(1))).toSet

  /** A lint may instead be pinned by a run golden (`// warning[W…]` lines): a warning does not fail. */
  private def lintInRunGoldens(c: Code): Boolean =
    c.lint.isDefined && files("tests/run", ".check").exists(p => Files.readString(p).contains(s"warning[${c.id}]"))

  private lazy val mainSources: List[(Path, String)] = files("src/main/scala", ".scala").map(p => p -> Files.readString(p))

  test("every active code is produced by a negative golden test (a lint possibly by a run golden)") {
    // the codes of the tools (the REPL, the language server) are not reported for programs
    val missing = Code.values
      .filter(c => c.isActive && c.phase != Phase.Tools && !reportedInGoldens(c.id) && !lintInRunGoldens(c))
      .map(_.id)
      .toList
    assertEquals(missing, Nil, "add a test in tests/neg for these codes")
  }

  test("retired codes appear in no golden test") {
    val retired = Code.values.filter(!_.isActive).map(_.id).toSet
    assertEquals(reportedInGoldens.intersect(retired), Set.empty[String])
  }

  test("no code is spelled as a string literal in the compiler") {
    val literal = "\"[EW]\\d{4}\"".r
    val offenders = for (p, text) <- mainSources if literal.findFirstIn(text).isDefined yield p.toString
    assertEquals(offenders, Nil, "use the `Code` constants")
  }

  test("every diagnostic of the compiler is a typed problem: no diagnostic is built from strings") {
    val offenders = for (p, text) <- mainSources if text.contains("Legacy.") yield p.toString
    assertEquals(offenders, Nil)
  }
