package hugin.util.diagnostics

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** Ties the registry to the tests and the sources: every active code has a negative golden test, retired
 *  codes are never reported, codes are never spelled as strings, and the `Legacy` escape hatch shrinks. */
class DiagnosticsCoverageSuite extends munit.FunSuite:
  /** The number of `Legacy` call sites when it was recorded. It may only go down: lower it when a phase
   *  migrates to its problem enum, never raise it (new code reports `Problem`s). */
  val LegacyBound = 167

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
    val missing = Code.values.filter(c => c.isActive && !reportedInGoldens(c.id) && !lintInRunGoldens(c)).map(_.id).toList
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

  test(s"the Legacy escape hatch has at most $LegacyBound call sites") {
    val count = legacyCallSites
    assert(count <= LegacyBound, s"$count Legacy call sites, more than the recorded $LegacyBound: report a `Problem` instead")
    if count < LegacyBound then println(s"note: Legacy call sites went down to $count; lower LegacyBound")
  }

  /** Each legacy call site names its code as a `Code` constant (possibly through a local helper, or as
   *  `DiagCode` where `Code` is taken by the meta type `MType.Code`), so the
   *  call sites are the code constants in the files using `Legacy`. */
  private def legacyCallSites: Int =
    val constant = "Code\\.[EW]\\d{4}".r
    mainSources
      .filter((p, text) => text.contains("Legacy.") && !p.toString.contains("util/diagnostics/"))
      .map((_, text) => constant.findAllMatchIn(text).size)
      .sum
