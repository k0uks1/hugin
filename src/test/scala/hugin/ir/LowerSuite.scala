package hugin.ir

import hugin.TestSupport

/** Lowering of core rules to the IR of Section 9.3. */
class LowerSuite extends munit.FunSuite:
  private def core(code: String): CoreProgram =
    val c = TestSupport.compile(code)
    assert(!c.reporter.hasErrors, c.reporter.diagnostics.map(_.message))
    c.unit.core.nn

  private def rule(p: CoreProgram, head: String): CompiledRule = p.rules.find(r => p.rels(r.headRel).name == head).get

  test("relations are tagged by position; components are evaluation-ordered tags") {
    val p = core("""
      e : int -> int -> rel.
      path : int -> int -> rel.
      path X Y :- e X Y.
      path X Z :- e X Y, path Y Z.
    """)
    p.rels.zipWithIndex.foreach((r, i) => assertEquals(r.tag, i))
    val e = p.rels.find(_.name == "e").get.tag
    val path = p.rels.find(_.name == "path").get.tag
    assert(p.components.indexWhere(_.contains(e)) < p.components.indexWhere(_.contains(path)), p.components)
  }

  test("atoms of the rule's own component are versioned scans; others are not") {
    val p = core("""
      e : int -> int -> rel.
      path : int -> int -> rel.
      path X Z :- e X Y, path Y Z.
    """)
    val r = rule(p, "path")
    assertEquals(r.recursiveAtoms, 1)
    val scans = r.body.toList.collect { case BodyOp.Scan(rel, recIdx, _, _, _) => (p.rels(rel).name, recIdx >= 0) }
    assertEquals(scans, List(("e", false), ("path", true)))
  }

  test("a scan with bound columns requests an index on them") {
    val p = core("""
      a : int -> rel.
      b : int -> int -> rel.
      q : int -> rel.
      q Y :- a X, b X Y.
    """)
    val b = p.rels.find(_.name == "b").get.tag
    assertEquals(p.indexes.get(b), Some(Set(Vector(0))))
  }

  test("negation, aggregation and comparison become NotIn, Agg and Test") {
    val p = core("""
      a : int -> rel.
      b : int -> rel.
      q : int -> int -> rel.
      q X N :- a X, not b X, N = count { Y | b Y }, X < N.
    """)
    val kinds = rule(p, "q").body.toList.map(_.getClass.getSimpleName)
    assert(kinds.contains("NotIn") && kinds.contains("Agg") && kinds.contains("Test"), kinds)
  }
