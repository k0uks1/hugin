package hugin.golden

import hugin.cli.Main

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** The programs of the website's language tour (`site/tour/X.hgn`, shown by `site/build.mjs` on the tour's
 *  pages and loaded into their editors), in a suite of their own: they load `std/semantics` and
 *  `std/strata`, which take seconds each, so they are kept out of the corpus-wide suites over `tests/run`.
 *
 *  - `site/tour/X.hgn`: compiled and run; stdout (after the warnings and other error output, as `// `
 *    lines) must equal `X.check`. `X.flags` holds extra command-line options (one line).
 *  - `site/tour/X-wrong.hgn`: a wrong proof that a lesson shows being rejected. It must fail to compile,
 *    and the rendered diagnostics must equal `X-wrong.check`.
 *
 *  Set `HUGIN_UPDATE_CHECKS=1` to (re)write the check files. */
class TourExamplesSuite extends munit.FunSuite:
  private val update = sys.env.get("HUGIN_UPDATE_CHECKS").contains("1")
  private val dir = Path.of("site", "tour")

  private val programs: List[Path] =
    if !Files.isDirectory(dir) then Nil
    else Files.list(dir).iterator().asScala.filter(_.toString.endsWith(".hgn")).toList.sortBy(_.toString)

  private def sibling(p: Path, ext: String): Path =
    val name = p.toString
    Path.of(name.substring(0, name.lastIndexOf('.')) + ext)

  private def flags(p: Path): List[String] =
    val f = sibling(p, ".flags")
    if Files.exists(f) then Files.readString(f).trim.split("\\s+").filter(_.nonEmpty).toList else Nil

  private def runMain(args: List[String]): (Int, String, String) =
    val out = new StringBuilder
    val err = new StringBuilder
    val code = Main.run(args :+ "--no-color", s => out ++= s += '\n', s => err ++= s += '\n')
    (code, out.toString, err.toString)

  private def compare(p: Path, actual: String): Unit =
    val check = sibling(p, ".check")
    if update || !Files.exists(check) then
      Files.writeString(check, actual)
      if !update then fail(s"no check file for $p; wrote ${check.getFileName}")
    else assertNoDiff(actual, Files.readString(check), s"output of $p differs from ${check.getFileName}")

  test("the tour has programs") {
    assert(programs.nonEmpty, s"no programs under $dir")
  }

  for p <- programs do
    val wrong = p.getFileName.toString.endsWith("-wrong.hgn")
    test(s"tour/${p.getFileName}") {
      if wrong then
        val (code, _, err) = runMain(List("check", p.toString) ++ flags(p))
        assertEquals(code, 1, s"expected errors in $p")
        compare(p, err)
      else
        val (code, out, err) = runMain(List("run", p.toString) ++ flags(p))
        assertEquals(code, 0, s"compilation or run failed:\n$err")
        val notes = if err.nonEmpty then err.linesIterator.map("// " + _).mkString("\n") + "\n" else ""
        compare(p, notes + out)
    }
