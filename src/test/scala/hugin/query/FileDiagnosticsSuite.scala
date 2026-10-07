package hugin.query

import hugin.util.*
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** Diagnostics by file ([[FileDiagnostics]]): read from the accumulators of the libraries' and the
 *  program's queries, they are the compilation's output, file by file. */
class FileDiagnosticsSuite extends munit.FunSuite:
  private def programs: List[Path] =
    List("run", "neg", "pos").flatMap { d =>
      val dir = Path.of("tests", d)
      if Files.isDirectory(dir) then Files.list(dir).iterator.asScala.filter(_.toString.endsWith(".hgn")).toList else Nil
    }.sortBy(_.toString)

  test("concatenated, the diagnostics by file are the compilation's output, for every golden program") {
    for p <- programs do
      given db: Database = Database()
      val key = CompileKey(p.toString)
      val byFile = FileDiagnostics.of(key)
      assertEquals(byFile.flatMap(_.diagnostics), db(Compile, key).diagnostics, p.toString)
      for f <- byFile do assert(f.diagnostics.forall(_.primarySpan.source.path == f.path), p.toString)
  }

  test("a library's diagnostics are its own file's, read from its queries without compiling it again") {
    given db: Database = Database()
    db.set(SourceText, "lib.hgn", "place : type.\nhere : place.\nbad X :- nothing X.\n")
    db.set(SourceText, "main.hgn", "g = %import \"lib\".\nat : g.place -> rel.\nat g.here.\nat X :- missing X.\n")
    db.set(SourceText, "other.hgn", "h = %import \"lib\".\n")
    val main = FileDiagnostics.of(CompileKey("main.hgn"))
    assertEquals(main.map(_.path), List("lib.hgn", "main.hgn"))
    assertEquals(main.map(_.diagnostics.flatMap(_.code).map(_.id)), List(List("E0101", "E0101"), List("E0101")))
    // another program importing the library: the library is not elaborated again, and has the same diagnostics
    db.stats.reset()
    val other = FileDiagnostics.of(CompileKey("other.hgn"))
    assertEquals(db.stats.computedBy("elabLibrary"), 0)
    assertEquals(other.find(_.path == "lib.hgn"), main.find(_.path == "lib.hgn"))
    // fixed: the library has no diagnostics left
    db.set(SourceText, "lib.hgn", "place : type.\nhere : place.\n")
    assertEquals(FileDiagnostics.of(CompileKey("main.hgn")).map(_.path), List("main.hgn"))
    assertEquals(FileDiagnostics.in(CompileKey("main.hgn"), "lib.hgn"), Nil)
  }

  test("a REPL-like program of several files has the diagnostics of each part in its own file") {
    given db: Database = Database()
    db.set(SourceText, "<input 1>", "p : int -> rel.\np X :- q X.\n")
    db.set(SourceText, "<input 2>", "r : int -> rel.\nr X :- s X.\n")
    db.set(Composite, "<session>", Vector(Part("<input 1>"), Part("<input 2>")))
    val key = CompileKey("<session>")
    val byFile = FileDiagnostics.of(key)
    assertEquals(byFile.map(_.path), List("<input 1>", "<input 2>"))
    assertEquals(byFile.flatMap(_.diagnostics), db(Compile, key).diagnostics)
  }
