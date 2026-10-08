package hugin.util.diagnostics

import hugin.TestSupport
import hugin.util.{Diagnostic, Severity, SourceFile}
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** The explanations `docs/errors/<id>.md`: one per code, each with examples that compile as documented.
 *  A ` ```hugin fail=<id> ` block must report `<id>` as its first error; a plain ` ```hugin ` block (the fix) must compile
 *  without errors and without that code. A ` ```facts ` block right after a `hugin` block is loaded as its
 *  input facts. Blocks tagged `new-meta` are elaborated by the new meta level (`hugin.core`, `--new-meta`).
 *  Blocks of retired codes are tagged `ignore` and skipped. */
class ExplanationsSuite extends munit.FunSuite:
  /** A code block of an explanation: the program, its expected code (for a failing example) and facts. */
  final case class Example(program: String, fails: Option[String], facts: Option[String], ignored: Boolean, newMeta: Boolean)

  private val dir = Path.of("docs/errors")
  private val fence = "(?ms)^```(\\w+)([^\\n]*)\\n(.*?)^```\\s*$".r

  private def examples(text: String): List[Example] =
    val blocks = fence.findAllMatchIn(text).map(m => (m.group(1), m.group(2).trim, m.group(3))).toList
    blocks.zipAll(blocks.drop(1).map(Some(_)), null, None).collect {
      case ((("hugin", attrs, body)), next) =>
        val facts = next.collect { case ("facts", _, f) => f }
        val fails = "fail=(\\S+)".r.findFirstMatchIn(attrs).map(_.group(1))
        Example(body, fails, facts, attrs.contains("ignore"), attrs.contains("new-meta"))
    }

  /** Compiles a program (and loads its facts, if it compiles); the diagnostics reported. */
  private def diagnostics(e: Example): List[Diagnostic] =
    if e.newMeta then hugin.core.NewMeta.check(SourceFile.virtual("test.hgn", e.program))
    else compiled(e)

  private def compiled(e: Example): List[Diagnostic] =
    val c = TestSupport.compile(e.program)
    val compiled = c.reporter.diagnostics
    e.facts match
      case Some(f) if !c.reporter.hasErrors =>
        compiled ++ hugin.runtime.Evaluation.run(c, List(SourceFile.virtual("test.facts", f))).diagnostics
      case _ => compiled

  private def file(c: Code): Path = dir.resolve(s"${c.id}.md")

  test("every code has an explanation, and every explanation is of a code") {
    val documented = Files.list(dir).iterator.asScala.map(_.getFileName.toString.stripSuffix(".md")).toSet
    assertEquals(Code.values.map(_.id).toSet -- documented, Set.empty[String], "codes without docs/errors/<id>.md")
    assertEquals(documented -- Code.values.map(_.id).toSet, Set.empty[String], "explanations of unknown codes")
  }

  for c <- Code.values.toList if Files.exists(file(c)) do
    test(s"${c.id}: the explanation's examples fail with ${c.id} and are fixed") {
      val text = Files.readString(file(c))
      assert(text.startsWith(s"# ${c.id}: ${c.title}\n"), s"${c.id}.md must start with `# ${c.id}: ${c.title}`")
      val all = examples(text).filterNot(_.ignored)
      if c.isActive then
        assert(all.exists(_.fails.contains(c.id)), s"${c.id}.md has no failing example")
        assert(all.exists(_.fails.isEmpty), s"${c.id}.md has no fixed example")
      for e <- all do
        val ds = diagnostics(e)
        e.fails match
          case Some(id) =>
            // the example shows this problem first: no other error comes before it
            val first = ds.find(d => d.severity == Severity.Error || d.code.exists(_.id == id))
            assertEquals(first.flatMap(_.code).map(_.id), Some(id), s"the first diagnostic of\n${e.program}\nis ${first.map(_.message)}")
          case None =>
            val errors = ds.filter(d => d.severity == Severity.Error || d.code.contains(c))
            assertEquals(errors.map(d => s"${d.code.fold("")(_.id)}: ${d.message}"), Nil, s"in the fixed example\n${e.program}")
    }
