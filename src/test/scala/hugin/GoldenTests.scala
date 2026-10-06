package hugin

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** Golden tests in the style of dotty's test suite.
 *
 *  - `tests/run/X.hgn`: compiled and run; stdout must equal `X.check`. Optional `X.facts` is loaded and
 *    `X.flags` holds extra command-line options (one line).
 *  - `tests/neg/X.hgn`: must fail to compile; the rendered diagnostics must equal `X.check`.
 *  - `tests/pos/X.hgn`: must compile without errors.
 *
 *  Set `HUGIN_UPDATE_CHECKS=1` to (re)write the check files.
 */
class GoldenTests extends munit.FunSuite:
  private val update = sys.env.get("HUGIN_UPDATE_CHECKS").contains("1")

  private def files(dir: String): List[Path] =
    val d = Path.of("tests", dir)
    if !Files.isDirectory(d) then Nil
    else Files.list(d).iterator().asScala.filter(_.toString.endsWith(".hgn")).toList.sortBy(_.toString)

  private def sibling(p: Path, ext: String): Path = Path.of(p.toString.stripSuffix(".hgn") + ext)

  private def flags(p: Path): List[String] =
    val f = sibling(p, ".flags")
    if Files.exists(f) then Files.readString(f).trim.split("\\s+").filter(_.nonEmpty).toList else Nil

  private def runMain(args: List[String]): (Int, String, String) =
    val out = new StringBuilder
    val err = new StringBuilder
    val code = Main.run("--no-color" :: args, s => out ++= s += '\n', s => err ++= s += '\n')
    (code, out.toString, err.toString)

  private def compare(p: Path, actual: String): Unit =
    val check = sibling(p, ".check")
    if update || !Files.exists(check) then
      Files.writeString(check, actual)
      if !update then fail(s"no check file for $p; wrote ${check.getFileName}")
    else
      val expected = Files.readString(check)
      assertNoDiff(actual, expected, s"output of $p differs from ${check.getFileName}")

  for p <- files("run") do
    test(s"run/${p.getFileName}") {
      val facts = sibling(p, ".facts")
      val factArgs = if Files.exists(facts) then List("--facts", facts.toString) else Nil
      val (code, out, err) = runMain(List("run", p.toString) ++ factArgs ++ flags(p))
      assertEquals(code, 0, s"compilation or run failed:\n$err")
      val warnings = if err.nonEmpty then err.linesIterator.map("// " + _).mkString("\n") + "\n" else ""
      compare(p, warnings + out)
    }

  for p <- files("neg") do
    test(s"neg/${p.getFileName}") {
      val (code, _, err) = runMain(List("check", p.toString) ++ flags(p))
      assertEquals(code, 1, s"expected compilation errors in $p")
      compare(p, err)
    }

  for p <- files("pos") do
    test(s"pos/${p.getFileName}") {
      val (code, _, err) = runMain(List("check", p.toString) ++ flags(p))
      assertEquals(code, 0, s"unexpected errors:\n$err")
    }
