package hugin.obj
package check

import hugin.TestSupport
import hugin.util.diagnostics.Code

/** Termination (Section 10) and the split rules of Proposition 8.8 (see docs/NOTES.md). */
class TerminationSuite extends munit.FunSuite:
  test("a rule of a fact constructor builds its head fact, even if its arguments are matched (E0603)") {
    val out = TestSupport.run("""
      t : type. z : t. s : t -> t.
      s (s z).
      s (s N) :- s N.
    """)
    assertEquals(out.left.toOption, Some(List("E0603")))
  }

  test("a fact term asserted in a later head that feeds its own constructor is checked in its component") {
    val c = TestSupport.compile("""
      t : type. z : t. s : t -> t.
      s z.
      d : t -> rel.
      d (s (s N)) :- s N.
    """)
    val d = c.reporter.diagnostics.filter(_.code == Code.E0603)
    assertEquals(d.length, 1)
    assert(d.head.notes.exists(_.contains("component {s}")), d.head.notes)
    assert(d.head.notes.exists(_.contains("is also evaluated in")), d.head.notes)
  }

  test("a fact constructor of an earlier component is a finite source") {
    // `mk` is complete after its component (its split rules run there), so `box M` takes finitely many values
    val out = TestSupport.run("""
      w : type. mk : int -> w. box : w -> w.
      src : int -> rel. src 1. src 2.
      g : w -> rel. g (mk N) :- src N.
      d : int -> w -> rel.
      d 0 (mk 1) :- src 1.
      d X (box (mk N)) :- d X _, mk N.
      %output d.
    """)
    assertEquals(out, Right(List("d 0 (box (mk 1)).", "d 0 (box (mk 2)).", "d 0 (mk 1).")))
  }
