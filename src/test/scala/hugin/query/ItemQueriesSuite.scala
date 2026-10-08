package hugin.query

import hugin.compiler.{Compiler, Parsed, Settings, SourceLoader}
import hugin.syntax.{Lexer, Tok}
import hugin.util.*
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import hugin.util.diagnostics.Code

/** Per-item elaboration (step 8 of `docs/INCREMENTALITY.md`) of items parsed from their own slices (step
 *  9): editing an item elaborates that item again, and the items whose inputs changed (those that use an
 *  edited declaration), not the others, also not the items the edit moved; the results equal those of a
 *  compilation from scratch, with the positions of the current text. */
class ItemQueriesSuite extends munit.FunSuite:
  private val settings = Settings(printAfter = Set("lower"))
  private val path = "items.hgn"

  private val program =
    """limit : int = 5.
      |n1 : type = int.
      |n2 : type = int.
      |p : int -> rel.
      |q : n1 -> rel.
      |r : int -> rel.
      |s : int -> rel.
      |t : int -> rel.
      |p 1.
      |p 2.
      |q 3.
      |r X :- p X, X < limit.
      |s X :- q X.
      |t X :- p X.
      |?- r X.
      |""".stripMargin

  /** The non-declaration items: facts, rules and the query. */
  private val items = 7

  private def setup(text: String = program): Database =
    val db = Database()
    db.set(SourceText, path, text)
    db

  private def compile(using db: Database): Compiled = db(Compile, CompileKey(path, settings))

  /** Edits the program and compiles it again, counting what was computed. */
  private def edit(from: String, to: String)(using db: Database): Unit =
    val text = db.get(SourceText, path)
    assert(text.contains(from), s"`$from` not in the program")
    db.set(SourceText, path, text.replace(from, to))
    db.stats.reset()
    compile

  private def elaborated(using db: Database): Int = db.stats.computedBy("elabItem")
  private def signatures(using db: Database): Int = db.stats.computedBy("signatures")

  test("the items of a program are elaborated one by one") {
    given db: Database = setup()
    val compiled = compile
    assert(!compiled.hasErrors, compiled.diagnostics)
    assertEquals(elaborated, items)
    assertEquals(signatures, 1)
  }

  test("editing a rule elaborates only that rule") {
    given db: Database = setup()
    compile
    edit("t X :- p X.", "t Y :- p Y.")
    assertEquals(elaborated, 1)
    assertEquals(signatures, 0)
    assertEquals(db.stats.computedBy("elabLibrary"), 0)
  }

  test("editing the last item elaborates only that item, also when its length changes") {
    given db: Database = setup()
    compile
    edit("?- r X.", "?- r X, t X.")
    assertEquals(elaborated, 1)
    assertEquals(signatures, 0)
  }

  test("an edit that changes the length of a rule elaborates only that rule, not the items it moves") {
    given db: Database = setup()
    compile
    // `t` and the query move; their slices are the same, so they are not elaborated again
    edit("s X :- q X.", "s X :- q X, p X.")
    assertEquals(elaborated, 1)
    assertEquals(signatures, 0)
  }

  test("blank lines and comments between items elaborate nothing") {
    given db: Database = setup()
    compile
    edit("p 1.\n", "\n\n(* a comment *)\np 1.\n")
    assertEquals(elaborated, 0)
    assertEquals(signatures, 0)
    edit("limit : int = 5.\n", "  (* first *)\n\n   limit : int = 5.\n")
    assertEquals(elaborated, 0)
    assertEquals(signatures, 0)
    edit("?- r X.", "?- r X.   (* the query *)")
    assertEquals(elaborated, 0)
    assertEquals(db.stats.computedBy("parseItem"), 0)
  }

  test("moving items elaborates nothing; positions are those of the current text") {
    given db: Database = setup(program.replace("t X :- p X.", "t X :- p Z."))
    compile
    val text = db.get(SourceText, path)
    // the items keep their text; every one of them moves (lines, columns and offsets change)
    val moved = "(* moved *)\n\n" + text.replace("p 1.\np 2.\n", "p 1.  p 2.\n").replace("n2 : type = int.\n", "\n  n2 : type = int.\n\n")
    db.set(SourceText, path, moved)
    db.stats.reset()
    val incremental = observe(moved)
    assertEquals(elaborated, 0)
    assertEquals(signatures, 0)
    assert(incremental._1.nonEmpty)
    assertEquals(rendered(incremental), rendered(fresh(moved)))
  }

  test("the items of the golden programs without parse errors are parsed from their slices") {
    for p <- programs do
      given db: Database = setup(Files.readString(p))
      val parsed = db(ParseProgram, path)
      if parsed.diagnostics.isEmpty then
        val whole = db(Parse, path).program.items
        assertEquals(parsed.program.items.count(!_.span.origin.isSlice), 0, p.toString)
        assert(hugin.syntax.Slices.congruent(parsed.program.items, whole), p.toString)
  }

  test("editing a meta definition elaborates the items that use it") {
    given db: Database = setup()
    compile
    edit("limit : int = 5.", "limit : int = 7.")
    assertEquals(signatures, 1)
    assertEquals(elaborated, 1) // the rule of `r`
  }

  test("editing an object declaration elaborates the items that use it") {
    given db: Database = setup()
    compile
    edit("q : n1 -> rel.", "q : n2 -> rel.")
    assertEquals(signatures, 1)
    assertEquals(elaborated, 2) // `q 3.` and the rule of `s`
  }

  test("an edit that moves lines elaborates only the edited item") {
    given db: Database = setup()
    compile
    edit("r X :- p X, X < limit.", "r X :-\np X, X < limit.")
    assertEquals(elaborated, 1) // `r`; `s`, `t` and the query are on other lines now, with the same slices
    val warned = program.replace("t X :- p X.", "t X :- p Z.")
    db.set(SourceText, path, warned)
    compile
    db.set(SourceText, path, warned.replace("q 3.", "q\n3."))
    assertEquals(rendered(observe(db.get(SourceText, path))), rendered(fresh(db.get(SourceText, path))))
  }

  test("adding a declaration elaborates no item; adding a meta definition only the items using its name") {
    given db: Database = setup()
    compile
    edit("t : int -> rel.\n", "t : int -> rel.\nu : int -> rel.\n")
    assertEquals(elaborated, 0)
    // the rule of `r` uses `limit` (from the top level); a new `X` would not change it, a shadowing `p` would
    edit("u : int -> rel.\n", "u : int -> rel.\nlimit2 : int = 3.\n")
    assertEquals(elaborated, 0)
    // a name that items look up and do not find (they fall through to the prelude) is a dependency too
    edit("r X :- p X, X < limit.", "r X :- p X, X < limit, X < lim.")
    assertEquals(elaborated, 1)
    assert(compile.diagnostics.exists(_.code.contains(Code.E0101)))
    edit("limit2 : int = 3.\n", "limit2 : int = 3.\nlim : int = 4.\n")
    assertEquals(elaborated, 1)
    assertEquals(rendered(observe(db.get(SourceText, path))), rendered(fresh(db.get(SourceText, path))))
  }

  test("a meta definition after an item is hidden from it (E0105) until it moves before it") {
    val text = program.replace("?- r X.", "?- r X.\nu : int -> rel.\nu X :- p X, X < late.\nlate : int = 2.")
    given db: Database = setup(text)
    compile
    assertEquals(compile.diagnostics.flatMap(_.code).map(_.id), List("E0105"))
    // moving the definition before the rule: the order changed, the rule is elaborated again
    edit("late : int = 2.\n", "")
    edit("limit : int = 5.\n", "limit : int = 5.\nlate : int = 2.\n")
    assertEquals(elaborated, 1)
    assertEquals(compile.diagnostics, Nil)
    assertEquals(rendered(observe(db.get(SourceText, path))), rendered(fresh(db.get(SourceText, path))))
  }

  test("a meta definition after a rule is used before its definition (E0105), also incrementally") {
    val late = program.replace("limit : int = 5.\n", "") + "limit : int = 5.\n"
    given db: Database = setup()
    compile
    db.set(SourceText, path, late)
    val compiled = compile
    assertEquals(compiled.diagnostics.flatMap(_.code).map(_.id), List("E0105"))
    assertEquals(rendered(observe(late)), rendered(fresh(late)))
    db.set(SourceText, path, program)
    assert(!compile.hasErrors, compile.diagnostics)
  }

  test("a program made of several files (a REPL session) elaborates only the items of a new part") {
    given db: Database = Database()
    db.set(SourceText, "in1.hgn", "p : int -> rel.\np 1.\np 2.\n")
    db.set(SourceText, "in2.hgn", "q : int -> rel.\nq X :- p X.\n")
    db.set(SourceText, "in3.hgn", "r : int -> rel.\nr X :- q X, p X.\n")
    db.set(Composite, "session", Vector(Part("in1.hgn"), Part("in2.hgn")))
    val key = CompileKey("session", settings)
    assert(!db(Compile, key).hasErrors)
    db.set(Composite, "session", Vector(Part("in1.hgn"), Part("in2.hgn"), Part("in3.hgn")))
    db.stats.reset()
    assert(!db(Compile, key).hasErrors)
    // the new declaration does not change the names the other items use: only the new rule is elaborated
    assertEquals(elaborated, 1)
    db.set(SourceText, "in4.hgn", "?- r X.\n")
    db.set(Composite, "session", Vector(Part("in1.hgn"), Part("in2.hgn"), Part("in3.hgn"), Part("in4.hgn")))
    db.stats.reset()
    assert(!db(Compile, key).hasErrors)
    assertEquals(elaborated, 1)
    assertEquals(signatures, 0)
  }

  // ------------------------------------------------------------------------- random edits of golden programs

  /** What a client observes: diagnostics, the printed lowered program, and at some names hover, the
   *  definition and the references (positions shown as `file:line:column`, so stale positions differ). */
  private def observe(text: String)(using db: Database): (List[Diagnostic], List[String], List[String]) =
    val key = CompileKey(path, settings)
    val compiled = db(Compile, key)
    val probes = Lexer(SourceFile.virtual(path, text), Reporter()).tokenize()
      .filter(t => t.kind == Tok.Name || t.kind == Tok.Var)
      .zipWithIndex.collect { case (t, i) if i % 4 == 0 => t.span.start + 1 }
      .take(30)
      .toList
    val ide = probes.map { o =>
      val refs = Ide.references(key, o).map(sp => s"${sp.show}-${sp.end}")
      s"${Ide.hover(key, o)} ${Ide.definition(key, o).map(_.show)} ${refs.mkString(" ")}"
    }
    val outline = Ide.symbols(key).map(d => s"${d.name} ${d.span.show} ${d.extent.show} ${d.container}")
    (compiled.diagnostics, compiled.printed, ide ++ outline)

  private def rendered(o: (List[Diagnostic], List[String], List[String])) =
    val renderer = DiagnosticRenderer(color = false)
    (o._1.map(renderer.render), o._1.map(_.primarySpan.show), o._2, o._3)

  private def fresh(text: String) = observe(text)(using setup(text))

  /** Compiles without a database (every part of the program in sequence): rendered diagnostics. */
  private def direct(text: String): List[String] =
    val loader: SourceLoader = p => (if p == path then Some(text) else SourceLoader.read(p)).map(t => Parsed(SourceFile.virtual(p, t)))
    val renderer = DiagnosticRenderer(color = false)
    Compiler.compileParsed(loader.load(path).get, settings, loader, _ => ()).reporter.sorted.map(renderer.render)

  private def programs: List[Path] =
    List("run", "neg", "pos").flatMap { d =>
      val dir = Path.of("tests", d)
      if Files.isDirectory(dir) then Files.list(dir).iterator.asScala.filter(_.toString.endsWith(".hgn")).toList else Nil
    }.sortBy(_.toString)

  /** A random edit of a program's lines: a character replaced, a line deleted, duplicated, moved or split. */
  private def randomEdit(text: String, rnd: scala.util.Random): String =
    val lines = text.linesIterator.toVector
    if lines.isEmpty then return "p : rel.\n"
    val i = rnd.nextInt(lines.length)
    val l = lines(i)
    val edited = rnd.nextInt(6) match
      case 0 if l.nonEmpty =>
        val j = rnd.nextInt(l.length)
        val c = "XYab01 .,:-()\n" (rnd.nextInt(14))
        lines.updated(i, l.substring(0, j) + c + l.substring(j + 1))
      case 1 => lines.patch(i, Nil, 1)
      case 2 => lines.patch(i, List(l, l), 1)
      case 3 =>
        val j = rnd.nextInt(lines.length)
        lines.updated(i, lines(j)).updated(j, l)
      case 4 => lines.patch(i, List(l, ""), 1)
      case _ => lines.patch(i, List("", l), 1)
    edited.mkString("", "\n", "\n")

  for p <- programs do
    test(s"incremental = from scratch under random edits: ${p.getParent.getFileName}/${p.getFileName}") {
      val rnd = scala.util.Random(p.getFileName.toString.hashCode)
      val original = Files.readString(p)
      given db: Database = setup(original)
      observe(original)
      var text = original
      for step <- 1 to 8 do
        text = randomEdit(text, rnd)
        db.set(SourceText, path, text)
        val incremental = observe(text)
        val scratch = fresh(text)
        assertEquals(rendered(incremental), rendered(scratch), s"after edit $step:\n$text")
        assertEquals(incremental._1.map(DiagnosticRenderer(color = false).render), direct(text), s"direct, after edit $step:\n$text")
      db.set(SourceText, path, original)
      assertEquals(rendered(observe(original)), rendered(fresh(original)))
    }

  // ------------------------------------------------------------------------------------------- eviction

  test("memos stay bounded under a long sequence of edits, and results equal those from scratch") {
    val original = Files.readString(Path.of("tests", "run", "f_modules.hgn"))
    def memos(text: String): Int =
      given db: Database = setup(text)
      compile
      db.memoCount
    val baseline = memos(original)
    val rnd = scala.util.Random(10)
    given db: Database = Database(collectAbove = baseline)
    db.set(SourceText, path, original)
    compile
    var text = original
    var max = 0
    for step <- 1 to 500 do
      // the edits drift away from the program; now and then it is restored
      text = if step % 50 == 0 then original else randomEdit(text, rnd)
      db.set(SourceText, path, text)
      compile
      max = max.max(db.memoCount)
      if step % 50 == 25 then assertEquals(rendered(observe(text)), rendered(fresh(text)), s"after edit $step:\n$text")
    assert(db.stats.collections > 0)
    assert(max <= 4 * baseline, s"$max memos after edits, $baseline for a compilation from scratch")
    // a collection now keeps what the current text needs (and the results of the previous epoch's)
    db.collect()
    assert(db.memoCount <= 2 * memos(text), s"${db.memoCount} memos kept, ${memos(text)} from scratch")
    // ... and after another edit and collection, only the slices and items of the current text
    db.set(SourceText, path, original)
    compile
    db.collect()
    db.set(SourceText, path, original + "\nlast : rel.\n")
    compile
    db.collect()
    val items = db(ParseProgram, path).program.items.length
    assertEquals(db.memoCount(ParseItem), items)
    assertEquals(db.memoCount(ItemOf), items - db(ScopeOf, ProgramKey(path, true)).declarations.length)
  }
