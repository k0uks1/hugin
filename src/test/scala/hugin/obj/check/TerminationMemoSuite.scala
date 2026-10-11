package hugin.obj.check

import hugin.compiler.Settings
import hugin.query.{Compile, CompileKey, Database, SourceText}
import hugin.util.DiagnosticRenderer

/** Termination verdicts that hold are memoised across compilations by their component up to symbols and
 *  positions ([[TerminationMemo]], issue #126, PR 6): an edit outside a component does not check it
 *  again, and every compilation reports what one from scratch reports. */
class TerminationMemoSuite extends munit.FunSuite:
  private val path = "memo_termination.hgn"
  private val program =
    """memo_up : int -> rel.
      |memo_up 0.
      |memo_up M :- memo_up N, M = N + 1, M <= 3.
      |memo_down : int -> rel.
      |memo_down 10.
      |memo_down M :- memo_down N, M = N - 1, M >= 0.
      |memo_other : int -> rel.
      |memo_other X :- memo_up X.
      |""".stripMargin

  private def computed = TerminationMemo.computed.get

  private def rendered(text: String, db: Database): List[String] =
    db.set(SourceText, path, text)
    db(Compile, CompileKey(path, Settings())).diagnostics.map(DiagnosticRenderer(color = false).render)

  private def fromScratch(text: String): List[String] = rendered(text, Database())

  test("an edit outside a component does not check its termination again") {
    val db = Database()
    rendered(program, db)
    val edits = List(
      program.replace("memo_other X :- memo_up X.", "memo_other X :- memo_up X, X > 0.") -> 0,
      program.replace("M <= 3", "M <= 4") -> 1,
      // moving the components (positions only) checks nothing again
      "\n\n(* moved *)\n" + program -> 0
    )
    for (text, expected) <- edits do
      val before = computed
      val incremental = rendered(text, db)
      assertEquals(computed - before, expected.toLong, text)
      assertEquals(incremental, fromScratch(text))
  }

  test("a rejected component is checked at every compilation and reported as from scratch") {
    val rejected = program.replace("M <= 3", "M > 0")
    val db = Database()
    val first = rendered(rejected, db)
    assert(first.exists(_.contains("E0603")), first)
    val edited = rejected.replace("memo_other X :- memo_up X.", "memo_other X :- memo_up X, X > 1.")
    val scratch = fromScratch(edited)
    val before = computed
    assertEquals(rendered(edited, db), scratch)
    assertEquals(computed - before, 1L) // `memo_up` again (rejected); `memo_down` memoised
  }
