package hugin.obj.transform

import hugin.TestSupport
import hugin.obj.ObjPrinter

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
