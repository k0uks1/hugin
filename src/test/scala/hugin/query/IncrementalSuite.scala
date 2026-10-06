package hugin.query

import hugin.compiler.Settings
import hugin.syntax.{Lexer, Tok}
import hugin.util.*
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** Incremental recompilation must agree with compilation from scratch. For every golden program, one
 *  database sees the original text, then edits (blank lines and a comment before every item, an extra
 *  item, the original again); after each edit its answers must equal those of a fresh database: the
 *  rendered diagnostics, the lowered program, and hover at a sample of identifiers. This is the safety
 *  net for finer-grained queries (issue #4), which must reuse results only when they are still valid. */
class IncrementalSuite extends munit.FunSuite:
  private val settings = Settings(printAfter = Set("lower"))
  private val path = "program.hgn"

  private def programs: List[Path] =
    List("run", "neg", "pos").flatMap { d =>
      val dir = Path.of("tests", d)
      if Files.isDirectory(dir) then Files.list(dir).iterator.asScala.filter(_.toString.endsWith(".hgn")).toList else Nil
    }.sortBy(_.toString)

  /** What a client observes about a program. */
  private def observe(text: String)(using db: Database): (List[String], List[String], List[Option[String]]) =
    val key = CompileKey(path, settings)
    val compiled = db(Compile, key)
    val renderer = DiagnosticRenderer(color = false)
    val diags = compiled.diagnostics.map(renderer.render)
    val probes = Lexer(SourceFile.virtual(path, text), Reporter()).tokenize()
      .filter(t => t.kind == Tok.Name || t.kind == Tok.Var)
      .zipWithIndex.collect { case (t, i) if i % 5 == 0 => t.span.start + 1 }
      .take(40)
      .toList
    (diags, compiled.printed, probes.map(o => Ide.hover(key, o)))

  private def fresh(text: String) =
    given db: Database = Database()
    db.set(SourceText, path, text)
    observe(text)

  /** Variants of a program that keep its meaning. */
  private def edits(text: String): List[String] =
    val lines = text.linesIterator.toList
    val spaced = lines.map(l => if l.nonEmpty && !l.head.isWhitespace then s"\n(* edit *)\n$l" else l).mkString("\n")
    List(spaced, text + "\nincremental_extra : rel.\n", text)

  for p <- programs do
    test(s"incremental = from scratch: ${p.getFileName}") {
      val original = Files.readString(p)
      given db: Database = Database()
      db.set(SourceText, path, original)
      assertEquals(observe(original), fresh(original))
      for text <- edits(original) do
        db.set(SourceText, path, text)
        assertEquals(observe(text), fresh(text), s"after an edit of ${p.getFileName}")
    }
