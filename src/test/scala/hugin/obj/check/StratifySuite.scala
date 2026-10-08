package hugin.obj
package check

import hugin.TestSupport
import hugin.util.diagnostics.Code

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
    val d = c.reporter.diagnostics.filter(_.code.contains(Code.E0601))
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

  // ---------------------------------------------------------------- Proposition 8.8: split rules

  private val nested = """
    w : type.
    %fact mk : int -> w.
    src : int -> rel.
    src 1.
    r : int -> rel.
    r N :- mk N.
    h : w -> rel.
    h (mk N) :- src N.
  """

  test("a fact term built in a head of a later component is split into its constructor's component") {
    val c = TestSupport.compile(nested)
    assert(!c.reporter.hasErrors, c.reporter.diagnostics.map(_.message))
    val comps = c.unit.components.map(_.map(_.name))
    def at(n: String) = comps.indexWhere(_.contains(n))
    // the split rule adds no edge: `mk` depends on `src` only, and `r` (reading `mk`) may come before `h`
    assertEquals(comps(at("mk")), List("mk"))
    assert(at("src") < at("mk") && at("mk") < at("r"), comps)
    val split = c.unit.prog.nn.rules.filter(c.unit.splitRules.contains)
    assertEquals(split.map(ObjPrinter.rule), Vector("mk N :- src N."))
    // the result is the least model, whatever the order of `r` and `h`
    assertEquals(TestSupport.run(nested + "%output r. %output h."), Right(List("h (mk 1).", "r 1.")))
  }

  test("no split rule when the constructor's component is not earlier, or for data constructors") {
    val c = TestSupport.compile("""
      w : type. %fact mk : int -> w. box : int -> w.
      src : int -> rel. src 1.
      h : w -> rel.
      h (mk N) :- src N.
      h (box N) :- src N.
      r : int -> rel. r N :- h (mk N).
    """)
    assert(!c.reporter.hasErrors, c.reporter.diagnostics.map(_.message))
    val comps = c.unit.components.map(_.map(_.name))
    // `mk` and `h` both depend on `src` only; if `mk` comes after `h`, `h`'s assertions precede it
    val mkFirst = comps.indexWhere(_.contains("mk")) < comps.indexWhere(_.contains("h"))
    assertEquals(c.unit.prog.nn.rules.count(c.unit.splitRules.contains), if mkFirst then 1 else 0)
  }

  test("an asserting rule that negates a reader of the constructor is a cycle through negation (E0601)") {
    val c = TestSupport.compile(nested.replace("h (mk N) :- src N.", "h (mk N) :- src N, not r N."))
    val d = c.reporter.diagnostics.filter(_.code.contains(Code.E0601))
    assertEquals(d.length, 1)
    assert(d.head.notes.exists(_.startsWith("cycle: mk -> not r -> mk")), d.head.notes)
    assert(d.head.notes.exists(_.contains("asserts facts of `mk` in its head")), d.head.notes)
  }

  test("an asserting rule aggregating over the constructor is a cycle through aggregation (E0601)") {
    val out = TestSupport.run("""
      w : type. %fact mk : int -> w.
      mk 1.
      h : w -> rel.
      h (mk C) :- C = count { N | mk N }.
    """)
    assertEquals(out.left.toOption, Some(List("E0601")))
  }

  test("aggregates and negations over a constructor see the facts asserted by later heads") {
    val out = TestSupport.run("""
      w : type. %fact mk : int -> w.
      mk 10.
      src : int -> rel. src 1. src 2.
      h : w -> rel. h (mk N) :- src N.
      total : int -> rel. total C :- C = count { N | mk N }.
      none : int -> rel. none N :- src N, not mk N.
      big : w -> rel. big (mk S) :- S = sum { N | src N }.
      %output total. %output none.
    """)
    assertEquals(out, Right(List("total 4.")))
  }

  test("the split rule depends on its rule's body only, not on the head relation's other rules") {
    val out = TestSupport.run("""
      w : type. %fact mk : int -> w.
      src : int -> rel. src 1.
      r : int -> rel. r N :- mk N.
      q : int -> rel. q N :- src N, not r 3.
      h : w -> rel.
      h (mk N) :- src N.
      h X :- q N, X = mk N.
      %output r. %output h.
    """)
    assertEquals(out, Right(List("h (mk 1).", "r 1.")))
  }
