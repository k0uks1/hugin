package hugin.obj.typing

import hugin.TestSupport

class ModingSuite extends munit.FunSuite:
  test("the canonical order reorders formulas so that every step is applicable (Lemma 6.4)") {
    val out = TestSupport.run("""
      e : int -> int -> rel.
      e 1 2. e 2 3.
      q : int -> int -> rel.
      q X Z :- Z = Y + 1, Y > 1, e X Y.
      %output q.
    """)
    assertEquals(out, Right(List("q 1 3.", "q 2 4.")))
  }

  test("range restriction and applicable modes are enforced (Section 6.3)") {
    assertEquals(TestSupport.run("p : int -> rel. p X :- X > 1.").left.toOption, Some(List("E0501")))
    assertEquals(
      TestSupport.run("f : (n : int) -> (m : int) -> rel. %mode f + -. f 1 2. q : int -> rel. q M :- f N M.").left.toOption,
      Some(List("E0502"))
    )
  }
