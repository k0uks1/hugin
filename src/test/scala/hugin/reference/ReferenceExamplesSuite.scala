package hugin.reference

import hugin.TestSupport
import hugin.reference.CodeBlocks.{Example, Mode}
import hugin.util.{Severity, SourceFile}
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** The code examples of the language reference (`reference/src/**/*.md`) compile, fail or run as their
 *  attributes say (see [[CodeBlocks]] and `reference/README.md`). The error index of the reference is
 *  made from `docs/errors/<code>.md`, whose examples are checked by `ExplanationsSuite`. */
class ReferenceExamplesSuite extends munit.FunSuite:
  private val root = Path.of("reference/src")

  private val pages: List[Path] =
    Files.walk(root).iterator.asScala.filter(_.toString.endsWith(".md")).toList.sorted

  private def name(page: Path): String = root.relativize(page).toString

  test("the reference has pages and Hugin examples") {
    assert(pages.nonEmpty, s"no pages under $root")
    val all = pages.flatMap(p => CodeBlocks.examples(Files.readString(p)).getOrElse(Nil))
    assert(all.exists(_.mode != Mode.Ignore), "no checked example: the pipeline would test nothing")
  }

  test("site-url.txt (the URL of the published book) and site-url of book.toml agree") {
    val url = java.net.URI(Files.readString(Path.of("reference/site-url.txt")).trim)
    val siteUrl = "(?m)^site-url = \"([^\"]*)\"".r.findFirstMatchIn(Files.readString(Path.of("reference/book.toml"))).map(_.group(1))
    assert(url.getPath.endsWith("/"), s"$url must end with /")
    assertEquals(siteUrl, Some(url.getPath))
  }

  for page <- pages do
    CodeBlocks.examples(Files.readString(page)) match
      case Left(problems) =>
        test(s"${name(page)}: code block attributes")(fail(problems.mkString("\n")))
      case Right(examples) =>
        for e <- examples if e.mode != Mode.Ignore do test(s"${name(page)}:${e.line}")(check(e))

  /** The diagnostics as `code: message`, for failure messages. */
  private def show(c: hugin.compiler.Context): String =
    c.reporter.diagnostics.map(d => s"${d.code.id}: ${d.message}").mkString("\n")

  private def check(e: Example): Unit =
    val c = TestSupport.compile(e.program)
    val errors = c.reporter.diagnostics.filter(_.severity == Severity.Error)
    e.mode match
      case Mode.CompileFail(code) =>
        assertEquals(errors.headOption.map(_.code.id), Some(code), s"the first error of\n${e.program}\n${show(c)}")
      case Mode.Compile =>
        assertEquals(errors.map(d => s"${d.code.id}: ${d.message}"), Nil, s"in\n${e.program}")
      case Mode.Run =>
        assertEquals(errors.map(d => s"${d.code.id}: ${d.message}"), Nil, s"in\n${e.program}")
        val facts = e.facts.toList.map(SourceFile.virtual("test.facts", _))
        val outcome = hugin.runtime.Evaluation.run(c, facts)
        val printed = outcome.result.map(_.output).getOrElse(Nil)
        val runErrors = outcome.diagnostics.filter(_.severity == Severity.Error).map(d => s"${d.code.id}: ${d.message}")
        assertEquals(runErrors, Nil, s"running\n${e.program}")
        assertEquals(printed.mkString("\n").trim, e.output.getOrElse("").trim, s"the output of\n${e.program}")
      case Mode.Ignore => ()
