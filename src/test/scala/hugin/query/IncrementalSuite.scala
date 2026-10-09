package hugin.query

import hugin.compiler.{Settings, StdlibCache}
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
  private def observe(text: String, path: String = path)(using db: Database): (List[String], List[String], List[Option[String]]) =
    val key = CompileKey(path, settings)
    val compiled = db(Compile, key)
    val renderer = DiagnosticRenderer(color = false)
    val diags = compiled.diagnostics.map(renderer.render)
    // the diagnostics by file, from the accumulators, are the compilation's output
    val byFile = FileDiagnostics.of(key)
    assertEquals(byFile.flatMap(_.diagnostics), compiled.diagnostics, s"diagnostics by file of $path")
    assertEquals(byFile.map(_.path).distinct.length, byFile.length)
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

  /** The files imported (transitively) by a golden program at its own path, which exist. */
  private def libraries(p: Path): List[String] =
    given db: Database = Database()
    // the files on disk: not the prelude, nor the bundled `std/` modules
    db(Compile, CompileKey(p.toString)).context.unit.libraries.values.map(_.path).filterNot(StdlibCache.isStdlib).toList

  for p <- programs if Files.readString(p).contains("%import") do
    test(s"incremental = from scratch under edits of imported files: ${p.getParent.getFileName}/${p.getFileName}") {
      val program = p.toString
      val original = Files.readString(p)
      val libs = libraries(p)
      assert(libs.nonEmpty || p.toString.contains("neg"), s"no imported files found for $p")
      var texts = (program :: libs).map(f => f -> Files.readString(Path.of(f))).toMap
      def fresh() =
        given db: Database = Database()
        texts.foreach((f, t) => db.set(SourceText, f, t))
        observe(original, program)
      given db: Database = Database()
      texts.foreach((f, t) => db.set(SourceText, f, t))
      assertEquals(observe(original, program), fresh())
      for lib <- libs; text <- edits(Files.readString(Path.of(lib))) do
        texts = texts.updated(lib, text)
        db.set(SourceText, lib, text)
        assertEquals(observe(original, program), fresh(), s"after an edit of $lib")
        // the program's own edits do not elaborate any library again
        db.stats.reset()
        db.set(SourceText, program, original + "\nincremental_extra : rel.\n")
        observe(original, program)
        assertEquals(db.stats.computedBy("elabLibrary"), 0, s"libraries elaborated again after editing $program")
        db.set(SourceText, program, original)
    }
