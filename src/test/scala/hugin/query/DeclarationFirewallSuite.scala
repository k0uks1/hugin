package hugin.query

import hugin.compiler.{Compiler, Settings, SourceLoader, StdlibCache}
import hugin.util.DiagnosticRenderer
import java.nio.file.{Files, Path}

/** An object item depends on what it read of its program's declarations, not on all of them (issue #126,
 *  PR 7 step 3; `docs/design/incrementality-2.md`, section 9): editing a declaration elaborates the items
 *  that read it, and every compilation equals one from scratch, also when a declaration changes a body
 *  that an item unfolds, is renamed, retyped, broken or removed, when an unresolved name becomes
 *  declared, and when a declaration added before the others shifts every global. */
class DeclarationFirewallSuite extends munit.FunSuite:
  private val settings = Settings(printAfter = Set("lower"))
  private val path = "firewall.hgn"

  private val program =
    """limit : int = 5.
      |double : int -> int = [x] x + x.
      |p : int -> rel.
      |q : int -> rel.
      |r : int -> rel.
      |s : int -> rel.
      |t : int -> rel.
      |u : int -> rel.
      |p 1.
      |p 2.
      |p 30.
      |r X :- p X, X < double limit.
      |s X :- p X, X < limit.
      |t X :- p X.
      |u X :- q X, X < missing.
      |?- r X.
      |""".stripMargin

  private def compile(text: String, db: Database): (List[String], List[String]) =
    db.set(SourceText, path, text)
    val c = db(Compile, CompileKey(path, settings))
    (c.diagnostics.map(DiagnosticRenderer(color = false).render), c.printed)

  private def direct(text: String): List[String] =
    val loader: SourceLoader = p => (if p == path then Some(text) else SourceLoader.read(p)).map(t => StdlibCache.parsed(p, t))
    Compiler.compileParsed(loader.load(path).get, settings, loader, _ => ()).reporter.sorted.map(DiagnosticRenderer(color = false).render)

  /** Applies the edits in turn: each compilation equals one from scratch (and the compiler's without the
   *  database); returns the number of items elaborated by each. */
  private def edits(steps: List[String => String]): List[Int] =
    val db = Database()
    var text = program
    compile(text, db)
    steps.map { f =>
      text = f(text)
      db.stats.reset()
      val incremental = compile(text, db)
      val elaborated = db.stats.computedBy("elabItem")
      assertEquals(incremental, compile(text, Database()), text)
      assertEquals(incremental._1, direct(text), text)
      elaborated
    }

  test("a changed body or type is seen by the items that read the declaration, and only by them") {
    // a fingerprint covers a definition's body (an item may unfold it)
    val bodies = edits(List(_.replace("[x] x + x", "[x] x * 3"), _.replace("limit : int = 5.", "limit : int = 2.")))
    assertEquals(bodies, List(1, 2)) // `r`; then `r` (through `double limit`) and `s`
    val types = edits(List(_.replace("double : int -> int = [x] x + x.", "double : float -> float = [x] x + x.")))
    assertEquals(types, List(1)) // `r`
    // a declaration dropped for an error leaves the scope: `u`, which has an unresolved name (and
    // depends on every name in scope, the designer's choice), is elaborated again too
    val dropped = edits(List(_.replace("double : int -> int = [x] x + x.", "double : int -> int = [x] x + .")))
    assertEquals(dropped, List(2))
  }

  test("renamed, retyped, broken and removed declarations") {
    edits(
      List(
        _.replace("limit : int = 5.", "bound : int = 5."),
        _.replace("bound : int = 5.", "limit : int = 5."),
        _.replace("limit : int = 5.", "limit : float = 5.0."),
        _.replace("limit : float = 5.0.", "limit : int = ."),
        _.replace("limit : int = .", ""),
        _.replace("double : int -> int", "double : float -> float")
      )
    )
  }

  test("an unresolved name becomes declared; a declaration added first shifts every global") {
    val counts =
      edits(List(_ + "missing : int = 10.\n", "first : type.\nother : first.\n" + _, _.replace("q : int -> rel.", "q : float -> rel.")))
    assertEquals(counts.head, 1) // `u`, which looked `missing` up
    assertEquals(counts(1), 0) // nothing reads `first` or `other`
  }

  test("long random edit sequences equal compilations from scratch") {
    val files = List("tests/run/a04_typechecker.hgn", "tests/run/f_modules.hgn", "tests/run/c2_module_wide.hgn", "examples/graphs.hgn")
    for f <- files if Files.exists(Path.of(f)) do
      val rnd = scala.util.Random(f.hashCode)
      val db = Database()
      var text = Files.readString(Path.of(f))
      compile(text, db)
      for step <- 1 to 25 do
        val lines = text.linesIterator.toVector
        val i = rnd.nextInt(lines.length.max(1))
        text = (rnd.nextInt(4) match
          case 0 if lines(i).nonEmpty =>
            val j = rnd.nextInt(lines(i).length)
            lines.updated(i, lines(i).substring(0, j) + "xa1 .:(" (rnd.nextInt(7)) + lines(i).substring(j + 1))
          case 1 => lines.patch(i, Nil, 1)
          case 2 => lines.patch(i, List(lines(i), lines(i)), 1)
          case _ => lines.updated(i, lines((i + 1) % lines.length)).updated((i + 1) % lines.length, lines(i))
        ).mkString("", "\n", "\n")
        assertEquals(compile(text, db), compile(text, Database()), s"$f, edit $step:\n$text")
  }
