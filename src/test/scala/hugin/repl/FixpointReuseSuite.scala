package hugin.repl

import java.nio.file.{Files, Path}

/** The REPL answers queries against the memoised fixpoint of the session's rules (`hugin.query.Fixpoint`)
 *  while the lowered rules and the facts are unchanged, and evaluates again when they change; answers are
 *  always those of a session evaluated from scratch. */
class FixpointReuseSuite extends munit.FunSuite:
  private val graph = List(
    "node : type = int.",
    "edge : node -> node -> rel. %input edge.",
    "path : node -> node -> rel.",
    "path X Y :- edge X Y.",
    "path X Z :- path X Y, edge Y Z."
  )
  private val edges = (1 to 30).map(i => s"edge $i ${i + 1}.").mkString("\n") + "\nedge 30 1.\n"

  private def tempFile(name: String, text: String): Path =
    val dir = Files.createTempDirectory("hugin-fixpoint")
    Files.writeString(dir.resolve(name), text)

  private def ok(s: Session, input: String): Reply =
    val r =
      if input.startsWith(":facts ") then s.loadFacts(input.drop(7))
      else if input.startsWith(":load ") then s.load(input.drop(6))
      else s.execute(input)
    assert(!r.hasErrors, s"unexpected errors for `$input`: ${r.diagnostics.map(_.message)}")
    r

  /** The answers of `query` in a new session of `inputs`: evaluated from scratch. */
  private def fromScratch(inputs: Seq[String], query: String): List[String] =
    val s = Session()
    inputs.foreach(ok(s, _))
    ok(s, query).output

  private def fixpoints(s: Session) = s.database.stats.computedBy("fixpoint")

  test("queries over unchanged rules and facts evaluate once; facts files are parsed once per text") {
    val facts = tempFile("g.facts", edges).toString
    val inputs = graph :+ s":facts $facts"
    val s = Session()
    inputs.foreach(ok(s, _))
    s.database.stats.reset()
    val queries = List("?- path 1 X.", "?- path X 3.", "?- path 5 5.", "?- path 1 X, path X 2.", "?- edge 30 X.", "?- path 1 X.")
    for q <- queries do assertEquals(ok(s, q).output, fromScratch(inputs, q), q)
    s.database.stats.reset()
    for q <- queries do ok(s, q)
    assertEquals(fixpoints(s), 0)
    assertEquals(s.database.stats.computedBy("factsFile"), 0)
    // a new rule changes the lowered rules: evaluated again, with its consequences
    ok(s, "loop : node -> rel.")
    ok(s, "loop X :- path X X.")
    s.database.stats.reset()
    assertEquals(ok(s, "?- loop 7.").output, List("yes."))
    assertEquals((fixpoints(s), s.database.stats.computedBy("factsFile")), (1, 0))
    ok(s, "?- loop 8.")
    assertEquals(fixpoints(s), 1)
  }

  test("a changed facts file evaluates again") {
    val file = tempFile("g.facts", "edge 1 2.\n")
    val s = Session()
    (graph :+ s":facts $file").foreach(ok(s, _))
    assertEquals(ok(s, "?- path 1 X.").output, List("X = 2."))
    Files.writeString(file, "edge 1 2.\nedge 2 3.\n")
    s.database.stats.reset()
    assert(!s.reload().hasErrors) // evaluates with the new facts, which the query reuses
    assertEquals(ok(s, "?- path 1 X.").output, List("X = 2.", "X = 3."))
    assertEquals((fixpoints(s), s.database.stats.computedBy("factsFile")), (1, 1))
  }

  test("a query that changes the demand-transformed rules evaluates again; answers equal from scratch") {
    val inputs = List(":load examples/typechecker.hgn", ":facts examples/typechecker.facts")
    val s = Session()
    inputs.foreach(ok(s, _))
    val queries = List(
      """?- typed (ref "x") (bind empty "x" (base "int")) T.""",
      """?- typed (ref "y") (bind empty "x" (base "int")) T.""",
      """?- result E T.""",
      """?- typed (ref "x") (bind empty "x" (base "int")) T."""
    )
    s.database.stats.reset()
    for q <- queries do assertEquals(ok(s, q).output, fromScratch(inputs, q), q)
    // the first two queries demand different contexts: two transformed programs
    assert(fixpoints(s) >= 2, fixpoints(s))
  }

  test("a fixpoint answers queries that check columns no rule indexes") {
    val s = Session()
    (graph ++ List("start : node -> rel. start 1.", "far : node -> node -> rel.", "far X Y :- start X, path X Y.")).foreach(ok(s, _))
    val facts = tempFile("g.facts", edges).toString
    ok(s, s":facts $facts")
    assertEquals(ok(s, "?- far 1 X.").output.length, 30 + 1) // the cycle reaches 1
    s.database.stats.reset()
    // `far` is read with its second column bound only here
    assertEquals(ok(s, "?- far X 17.").output, List("X = 1."))
    assertEquals(ok(s, "?- far X 99.").output, List("no."))
    assertEquals(fixpoints(s), 0)
  }
