package hugin.obj.transform

import hugin.TestSupport
import hugin.obj.ObjPrinter
import hugin.util.diagnostics.Code

/** The object-level transformations of Section 7. */
class TransformSuite extends munit.FunSuite:
  test("equal rules under %derivations each get their derivation relation and rule (Section 7.4)") {
    val out = TestSupport.run("""
      e : int -> rel. e 1.
      p : int -> rel.
      @r p X :- e X.
      @r p X :- e X.
      %derivations p.
    """)
    assertEquals(out, Right(List("@r#1 (p 1) (e 1).", "@r#2 (p 1) (e 1).")))
  }

  test("demand propagation rules are deduplicated structurally (Section 7.3)") {
    val c = TestSupport.compile("""
      e : int -> int -> rel.
      e 1 2. e 2 3.
      reach : int -> int -> rel.
      %mode reach + -.
      reach X Y :- e X Y.
      reach X Z :- e X Y, reach Y Z.
      ?- reach 1 Z.
      ?- reach 1 Z.
    """)
    assert(!c.reporter.hasErrors, c.reporter.diagnostics.map(_.message))
    val demandRules = c.unit.prog.nn.rules.filter(_.heads.exists(h => ObjPrinter.term(h).startsWith("reach^d"))).map(ObjPrinter.rule)
    assertEquals(demandRules.distinct, demandRules)
    assertEquals(demandRules.length, 2, demandRules)
  }

  // ---------------------------------------------------------------- demand per call site

  private val lists = """
    e : list int -> rel.
    e nil. e (cons 1 nil). e (cons 2 (cons 1 nil)).
    a : list int -> int -> rel.
    a L N :- e L, len L N.
  """

  private def copies(c: hugin.compiler.Context): List[String] =
    c.unit.prog.nn.rels.toList.map(_.name).filter(n => n.contains("#") && !n.contains("^d"))

  test("a call whose demand negates a caller of the callee gets its own copy (no E0601)") {
    val code = lists + """
      b : list int -> int -> rel.
      b L N :- e L, not a L 1, len L N.
      %output b.
    """
    val c = TestSupport.compile(code)
    assert(!c.reporter.hasErrors, c.reporter.diagnostics.map(_.message))
    // only `b`'s call is copied; `a`'s call keeps the shared demand relation
    assertEquals(copies(c), List("len[int]#1"))
    assert(c.unit.prog.nn.rules.exists(r => ObjPrinter.rule(r) == "a L N :- e L, len[int] L N."))
    assertEquals(TestSupport.run(code), Right(List("b (cons 2 (cons 1 nil)) 2.", "b nil 0.")))
  }

  test("a call whose input is computed by an aggregate over a caller of the callee") {
    val code = lists + """
      c : int -> int -> rel.
      c M K :- M = count { L | a L _ }, len (cons M (cons M nil)) K.
      %output c.
    """
    assertEquals(TestSupport.run(code), Right(List("c 3 2.")))
  }

  test("two calls with a disjunction inside an aggregate between them") {
    val code = lists + """
      f : int -> rel. f 0. f 5.
      g : int -> int -> rel. g 7 1. g 8 2. g 9 2.
      s : list int -> int -> int -> rel.
      s L N M :- e L, len L N, C = count { X | f X ; g X N }, V = cons C L, len V M.
      %output s.
    """
    assertEquals(
      TestSupport.run(code),
      Right(List("s (cons 1 nil) 1 2.", "s (cons 2 (cons 1 nil)) 2 3.", "s nil 0 1."))
    )
  }

  test("copies are checked for termination like the relation they copy") {
    val c = TestSupport.compile(
      lists + "b : list int -> int -> rel. b L N :- e L, not a L 1, len L N.",
      hugin.compiler.Settings(explainTermination = true)
    )
    assert(!c.reporter.hasErrors, c.reporter.diagnostics.map(_.message))
    assert(c.unit.explanations.exists(_.startsWith("termination: {len[int]#1}: terminates")), c.unit.explanations)
  }

  test("a cycle through negation that copies do not break is reported on the shared transformation") {
    val c = TestSupport.compile(lists + "b : list int -> int -> rel. b L N :- e L, not b L 0, len L N.")
    val d = c.reporter.diagnostics.filter(_.code.contains(Code.E0601))
    assertEquals(d.length, 1)
    assert(!d.head.notes.exists(_.contains("#")), d.head.notes)
    assertEquals(copies(c), Nil)
  }
