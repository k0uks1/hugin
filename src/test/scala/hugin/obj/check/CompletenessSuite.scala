package hugin.obj
package check

import hugin.TestSupport
import hugin.util.diagnostics.Code

/** The completeness discipline (Section 6.5, Definition 6.6). */
class CompletenessSuite extends munit.FunSuite:
  private def errors(code: String) =
    TestSupport.compile(code).reporter.diagnostics.filter(_.code.contains(Code.E0602))

  test("negating a complete relation is accepted") {
    assertEquals(
      TestSupport.run("""
        e : int -> rel.
        e 1.
        d : int -> rel.
        d 1. d 2.
        p : int -> rel.
        p X :- d X, not e X.
        %output p.
      """),
      Right(List("p 2."))
    )
  }

  test("negating an open relation is an error that says why it is incomplete") {
    val ds = errors("""
      e : int -> rel.
      %open e.
      d : int -> rel.
      p : int -> rel.
      p X :- d X, not e X.
    """)
    assertEquals(ds.length, 1)
    assert(ds.head.notes.contains("`e` is declared %open"), ds.head.notes)
  }

  test("incompleteness propagates along positive dependencies") {
    val ds = errors("""
      e : int -> rel.
      %open e.
      f : int -> rel.
      f X :- e X.
      d : int -> rel.
      p : int -> rel.
      p N :- d N, N = count { X | f X }.
    """)
    assertEquals(ds.length, 1)
    assert(ds.head.notes.contains("`f` depends positively on `e`; `e` is declared %open"), ds.head.notes)
  }

  test("queries may mention incomplete relations only positively") {
    val code = """
      e : int -> rel.
      %open e.
      d : int -> rel.
    """
    assertEquals(errors(code + "?- e X.").length, 0)
    val ds = errors(code + "?- d X, not e X.")
    assertEquals(ds.map(_.message), List("query negates or aggregates over the incomplete relation `e`"))
  }

  test("the incomplete relations are a result of the unit, not state of the phase object") {
    val a = TestSupport.compile("x : int -> rel. %open x. y : int -> rel. y N :- x N.")
    val b = TestSupport.compile("z : int -> rel. %open z. z 1.")
    assertEquals(a.unit.incomplete.map(_.name), Set("x", "y"))
    assertEquals(b.unit.incomplete.map(_.name), Set("z"))
    // one phase object serves both units
    val phase = CompletenessPhase()
    phase.run(using b)
    phase.run(using a)
    assertEquals(phase.show(using b), "incomplete: z")
    assertEquals(phase.show(using a), "incomplete: x, y")
  }
