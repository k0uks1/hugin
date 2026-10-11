package hugin.query

import hugin.compiler.{Compiler, Settings, SourceLoader, StdlibCache}
import hugin.syntax.TreeOps.hasSyntaxErrors
import hugin.util.*

/** A rule or query with a syntax error is filed with the declarations as a stand-in
 *  (`hugin.core.elab.BrokenItems`): typing inside a rule elaborates the declarations again only when
 *  the rule starts or stops parsing (or the names it might declare change), and every state of the text
 *  compiles as from scratch (issue #126, PR 1). */
class BrokenItemsSuite extends munit.FunSuite:
  private val settings = Settings(printAfter = Set("lower"))
  private val path = "broken.hgn"

  private val program =
    """limit : int = 5.
      |p : int -> rel.
      |q : int -> rel.
      |r : int -> rel.
      |even : int -> prop.
      |even X = X = 0.
      |p 1.
      |p 2.
      |q X :- p X, X < limit.
      |?- q X.
      |""".stripMargin

  private def direct(text: String): List[String] =
    val loader: SourceLoader = p => (if p == path then Some(text) else SourceLoader.read(p)).map(t => StdlibCache.parsed(p, t))
    val renderer = DiagnosticRenderer(color = false)
    Compiler.compileParsed(loader.load(path).get, settings, loader, _ => ()).reporter.sorted.map(renderer.render)

  /** Types `typed` before the query, one character at a time; at each step the compilation equals one
   *  from scratch. Returns, per step, whether the declarations were elaborated, whether they contain a
   *  stand-in, and their fingerprints. */
  private def typing(typed: String): List[(Boolean, Boolean, List[ItemFingerprint])] =
    val db = Database()
    val at = program.indexOf("?-")
    db.set(SourceText, path, program)
    db(Compile, CompileKey(path, settings))
    for i <- (1 to typed.length).toList yield
      val text = program.take(at) + typed.take(i) + program.drop(at)
      db.set(SourceText, path, text)
      db.stats.reset()
      val compiled = db(Compile, CompileKey(path, settings))
      val renderer = DiagnosticRenderer(color = false)
      assertEquals(compiled.diagnostics.map(renderer.render), direct(text), s"after typing ${typed.take(i)}")
      val decls = db(DeclarationsOf, ProgramKey(path, true))
      (db.stats.computedBy("signatures") > 0, decls.items.exists(hasSyntaxErrors), decls.fingerprints)

  test("typing a rule elaborates the declarations only when it starts or stops parsing") {
    val typed = "r X :- p X, q X, X > 1.\n"
    val steps = typing(typed)
    // most states do not parse (the rule runs into the query until its period)
    assert(steps.count(_._2) >= typed.length - 2, steps.map(_._2))
    // the declarations are elaborated exactly when what they read changed: when the rule starts or stops
    // parsing, when it mentions another declared name (`p`, `q`: the order of elaboration depends on
    // them), and in the one state where it reads as a broken declaration (`r X :`), kept as it is
    val changed = steps.indices.filter(i => i == 0 || steps(i)._3 != steps(i - 1)._3)
    assertEquals(steps.indices.filter(steps(_)._1), changed)
    assert(changed.length <= 7, changed)
  }

  test("a broken clause of a formula function and a broken query compile as from scratch") {
    typing("even X = X = 2 ; X = .\n")
    typing("?- p X, \n")
    typing("@named r X :- p (X.\n")
  }
