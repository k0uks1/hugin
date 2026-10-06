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

  test("directives are phase output in the unit's facts; the core IR carries them by tag") {
    val c = TestSupport.compile("""
      f : (n : int) -> (m : int) -> rel.
      %mode f + -. %mode f + +. %partial f.
      f 1 2.
      q : int -> rel.
      q M :- f 1 M.
      %output q.
    """)
    assert(!c.reporter.hasErrors, c.reporter.diagnostics.map(_.message))
    val f = c.unit.prog.nn.rels.find(_.name == "f").get
    val facts = c.unit.facts
    assertEquals(facts.modesOf(f).map(_.show), List("+-", "++"))
    assert(facts(f).partial && !facts(f).output)
    val core = c.unit.core.nn
    assertEquals(core.directives.length, core.rels.length)
    assert(core.directives(core.tag(f)).partial)
    val q = core.rels.find(_.name == "q").get
    assert(core.directives(core.tag(q)).output)
    // a relation without directives reads as none (all outputs, complete)
    assertEquals(facts.modesOf(q).map(_.show), List("-"))
  }
