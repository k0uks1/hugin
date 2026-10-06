package hugin.obj
package check

import hugin.TestSupport

/** Stratification (Section 6.4): components in dependency order, cycles through negation. */
class StratifySuite extends munit.FunSuite:
  test("components come in dependency order; mutually recursive relations share one") {
    val c = TestSupport.compile("""
      e : int -> int -> rel.
      a : int -> rel.
      b : int -> rel.
      top : int -> rel.
      a X :- e X _.
      a X :- b X.
      b X :- a X, e _ X.
      top X :- b X, not e X X.
    """)
    assert(!c.reporter.hasErrors, c.reporter.diagnostics.map(_.message))
    val comps = c.unit.components.map(_.map(_.name).toSet)
    def at(n: String) = comps.indexWhere(_(n))
    assertEquals(comps(at("a")), Set("a", "b"))
    assert(at("e") < at("a") && at("a") < at("top"), comps)
  }

  test("a cycle through negation is reported with the cycle (E0601)") {
    val c = TestSupport.compile("""
      e : int -> rel.
      p : int -> rel.
      q : int -> rel.
      p X :- e X, not q X.
      q X :- e X, p X.
    """)
    val d = c.reporter.diagnostics.filter(_.code.contains("E0601"))
    assertEquals(d.length, 1)
    assert(d.head.notes.exists(_.startsWith("cycle: p -> not q -> p")), d.head.notes)
  }

  test("an aggregate over a lower stratum is accepted, over its own component not") {
    assertEquals(
      TestSupport.run("""
        e : int -> rel.
        e 1. e 2.
        n : int -> rel.
        n N :- N = count { X | e X }.
        %output n.
      """),
      Right(List("n 2."))
    )
    assertEquals(
      TestSupport.run("""
        n : int -> rel.
        n 0.
        n N :- N = count { X | n X }.
      """).left.toOption,
      Some(List("E0601"))
    )
  }
