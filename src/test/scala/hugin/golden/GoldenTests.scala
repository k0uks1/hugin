package hugin.golden

import hugin.cli.Main

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** Golden tests in the style of dotty's test suite.
 *
 *  - `tests/run/X.hgn`: compiled and run; stdout must equal `X.check`. Optional `X.facts` is loaded and
 *    `X.flags` holds extra command-line options (one line).
 *  - `tests/neg/X.hgn`: must fail to compile (or, with `X.facts`, to load its input); the rendered
 *    diagnostics must equal `X.check`. Inline annotations `(*~ E0603 *)`, if the file has any, must match
 *    the codes and lines reported (see [[Annotations]]).
 *  - `tests/recovery/X.hgn`: programs with syntax errors (issue #53). They must fail to compile; their
 *    inline annotations (required) must account for exactly the diagnostics reported, so that an error
 *    that follows from a syntax error (a cascading error) fails the test; `X.check` holds the diagnostics
 *    and the program after `elaborate`, which shows that the items around the errors are elaborated.
 *  - `tests/pos/X.hgn`: must compile without errors.
 *  - `docs/design/examples/X.hgn`: the worked examples of the design notes, run like `tests/run`.
 *  - `site/X.hgn`: the examples of the website's landing page (site/build.mjs shows their `.check`),
 *    run like `tests/run`.
 *  - `tests/json/X.hgn`: checked with `--error-format=json`; the JSON lines on stderr must equal `X.check`.
 *  - `tests/fix/X.hgn`: a copy is fixed by `hugin fix` (rustfix); the result must equal `X.fixed`, compile
 *    without errors, and be a fixed point (fixing it again changes nothing).
 *  - `tests/annotations/X.hgn`: the annotation table of the program (`hugin.ide.Annotations`: every name
 *    with its hover, declaration and occurrence group, the hovers, the inlay hints), rendered as text, must
 *    equal `X.check`.
 *  - `tests/repl/X.in`: a REPL session, run by `hugin repl --batch --echo`; the transcript (inputs after
 *    their prompts, output and diagnostics) must equal `X.check`. `X.flags` holds extra options (e.g.
 *    files to load).
 *
 *  Set `HUGIN_UPDATE_CHECKS=1` to (re)write the check files.
 */
class GoldenTests extends munit.FunSuite:
  private val update = sys.env.get("HUGIN_UPDATE_CHECKS").contains("1")

  private def files(dir: String, ext: String = ".hgn", root: String = "tests"): List[Path] =
    val d = Path.of(root, dir)
    if !Files.isDirectory(d) then Nil
    else Files.list(d).iterator().asScala.filter(_.toString.endsWith(ext)).toList.sortBy(_.toString)

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

  private def compare(p: Path, actual: String, ext: String = ".check"): Unit =
    val check = sibling(p, ext)
    if update || !Files.exists(check) then
      Files.writeString(check, actual)
      if !update then fail(s"no check file for $p; wrote ${check.getFileName}")
    else
      val expected = Files.readString(check)
      assertNoDiff(actual, expected, s"output of $p differs from ${check.getFileName}")

  for p <- files("run") ++ files("design/examples", root = "docs") ++ files("", root = "site") do
    test(s"${p.getParent.getFileName}/${p.getFileName}") {
      val facts = sibling(p, ".facts")
      val factArgs = if Files.exists(facts) then List("--facts", facts.toString) else Nil
      val (code, out, err) = runMain(List("run", p.toString) ++ factArgs ++ flags(p))
      assertEquals(code, 0, s"compilation or run failed:\n$err")
      val warnings = if err.nonEmpty then err.linesIterator.map("// " + _).mkString("\n") + "\n" else ""
      compare(p, warnings + out)
    }

  for p <- files("neg") do
    test(s"neg/${p.getFileName}") {
      val facts = sibling(p, ".facts")
      val cmd = if Files.exists(facts) then List("run", p.toString, "--facts", facts.toString) else List("check", p.toString)
      val (code, _, err) = runMain(cmd ++ flags(p))
      assertEquals(code, 1, s"expected errors in $p")
      val expected = Annotations.expected(Files.readString(p))
      if expected.nonEmpty then assertEquals(Annotations.reported(err, p.toString), expected, s"annotations of $p")
      compare(p, err)
    }

  for p <- files("recovery") do
    test(s"recovery/${p.getFileName}") {
      val (code, out, err) = runMain(List("check", p.toString, "--print-after", "elaborate") ++ flags(p))
      assertEquals(code, 1, s"expected errors in $p")
      val expected = Annotations.expected(Files.readString(p))
      assert(expected.nonEmpty, s"$p has no annotations")
      assertEquals(Annotations.reported(err, p.toString), expected, s"annotations of $p")
      compare(p, err + out)
    }

  for p <- files("json") do
    test(s"json/${p.getFileName}") {
      val (_, _, err) = runMain(List("check", p.toString, "--error-format=json") ++ flags(p))
      compare(p, err)
    }

  for p <- files("fix") do
    test(s"fix/${p.getFileName}") {
      val dir = Files.createTempDirectory("hugin-fix")
      val copy = dir.resolve(p.getFileName)
      try
        Files.copy(p, copy)
        runMain(List("fix", copy.toString) ++ flags(p))
        val fixed = Files.readString(copy)
        compare(p, fixed, ".fixed")
        val (code, _, err) = runMain(List("check", copy.toString) ++ flags(p))
        assertEquals(code, 0, s"the fixed program has errors:\n$err")
        runMain(List("fix", copy.toString) ++ flags(p))
        assertNoDiff(Files.readString(copy), fixed, "fixing again changed the program")
      finally
        Files.deleteIfExists(copy)
        Files.deleteIfExists(dir)
    }

  for p <- files("pos") do
    test(s"pos/${p.getFileName}") {
      val (code, _, err) = runMain(List("check", p.toString) ++ flags(p))
      assertEquals(code, 0, s"unexpected errors:\n$err")
    }

  for p <- files("annotations") do
    test(s"annotations/${p.getFileName}") {
      given db: hugin.query.Database = hugin.query.Database()
      val path = p.toString
      db.set(hugin.query.SourceText, path, Files.readString(p))
      compare(p, renderAnnotations(hugin.ide.Annotations.of(hugin.query.CompileKey(path), path)))
    }

  /** An annotation table as text: positions are `line:column`, 1-based, columns in UTF-16 code units. */
  private def renderAnnotations(a: hugin.ide.Annotations): String =
    def at(sp: hugin.util.Span, offset: Int) =
      val line = sp.source.lineOf(offset)
      s"${line + 1}:${offset - sp.source.lineStart(line) + 1}"
    def range(sp: hugin.util.Span) = s"${at(sp, sp.start)}-${at(sp, sp.end)}"
    def indent(text: String) = text.linesIterator.map(_.stripTrailing).mkString("\n      ")
    val names = a.names.map { n =>
      val target = n.target.fold("") {
        case hugin.ide.Target.InFile(sp) => s"  -> ${at(sp, sp.start)}"
        case hugin.ide.Target.Library(module, name) => s"  -> $module.$name"
      }
      val hover = if n.hover < 0 then "" else s"  hover ${n.hover}"
      s"  ${range(n.span)} `${n.span.text}`  group ${n.group}${if n.declaration then "  declaration" else ""}$hover$target"
    }
    val hovers = a.hovers.toList.zipWithIndex.map { (h, i) =>
      (s"  $i   ${h.signature.fold("(no signature)")(indent)}" :: h.notes.map(nt => s"      ${indent(nt)}")).mkString("\n")
    }
    val hints = a.hints.map(h => s"  ${at(h.at, h.at.start)} `${h.label}` (${h.kind})")
    (List("names:") ++ names ++ List("hovers:") ++ hovers ++ List("hints:") ++ hints).mkString("", "\n", "\n")

  for p <- files("repl", ".in") do
    test(s"repl/${p.getFileName}") {
      val transcript = new StringBuilder
      val print = (s: String) => { transcript ++= s += '\n'; () }
      val in = Files.newInputStream(p)
      try Main.run(List("repl", "--batch", "--echo", "--no-color") ++ flags(p), print, print, in)
      finally in.close()
      compare(p, transcript.toString)
    }
