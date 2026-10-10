package hugin.core

import CoreTesting.*
import hugin.util.diagnostics.Code

/** Pattern matching: case trees from clauses, dependent matching with index unification, coverage
 *  (including impossible cases), and compile-time evaluation. */
class ClausesSuite extends munit.FunSuite:
  private val nat =
    """nat : Type.
      |zero : nat.
      |suc : nat -> nat.
      |plus : nat -> nat -> nat.
      |plus zero N = N.
      |plus (suc M) N = suc (plus M N).
      |""".stripMargin

  private val vec = nat +
    """vec : Type -> nat -> Type.
      |vnil : vec A zero.
      |vcons : A -> vec A N -> vec A (suc N).
      |""".stripMargin

  test("plus evaluates at compile time") {
    val e = ok(nat)
    assertEquals(e.eval("plus 2 3"), "5")
    assertEquals(e.eval("[n : nat] plus zero n"), "[n] n")
    assertEquals(e.eval("[n : nat] plus n zero"), "[n] plus n 0")
  }

  test("head needs no vnil clause: the case is impossible by index unification") {
    val e = ok(vec + "head : vec A (suc N) -> A.\nhead (vcons X _) = X.\n")
    assertEquals(e.eval("head (vcons 1 (vcons 2 vnil))"), "1")
  }

  test("dependent matching refines types: append, tail") {
    val e = ok(vec +
      """append : vec A N -> vec A M -> vec A (plus N M).
        |append vnil YS = YS.
        |append (vcons X XS) YS = vcons X (append XS YS).
        |tail : vec A (suc N) -> vec A N.
        |tail (vcons _ XS) = XS.
        |""".stripMargin)
    assertEquals(e.eval("tail (append (vcons 1 vnil) (vcons 2 vnil))"), "vcons {int} {0} 2 (vnil {int})")
  }

  test("an argument with no possible constructor needs no clause (absurd)") {
    ok(vec +
      """fin : nat -> Type.
        |fz : fin (suc N).
        |fs : fin N -> fin (suc N).
        |lookup : vec A N -> fin N -> A.
        |lookup (vcons X _) fz = X.
        |lookup (vcons _ XS) (fs I) = lookup XS I.
        |""".stripMargin)
  }

  test("missing cases are reported with the missing pattern") {
    val text = firstError(nat + "pred : nat -> nat.\npred (suc N) = N.\n")
    assert(text.contains("error[E0911]"), text)
    assert(text.contains("missing: `pred 0`"), text)
    val text2 = firstError(vec + "first : vec A N -> A.\nfirst (vcons X _) = X.\n")
    assert(text2.contains("missing: `first vnil`"), text2)
  }

  test("unreachable clauses are warned about") {
    val e = ok(nat + "isZero : nat -> nat.\nisZero zero = 1.\nisZero N = 0.\nisZero (suc N) = 0.\n")
    assert(e.diagnostics.exists(_.code == Code.W0006))
  }

  test("pattern errors") {
    assertEquals(errors(nat + "f : nat -> nat -> nat.\nf N N = N.\n"), List("E0915"))
    assertEquals(errors(nat + "f : nat -> nat.\nf (suc) = zero.\nf zero = zero.\n"), List("E0915"))
    assertEquals(errors(nat + "f : int -> nat.\nf zero = zero.\n"), List("E0915"))
    assertEquals(errors(nat + "f : nat -> nat.\nf zero = zero.\nf (suc N) M = zero.\n"), List("E0915"))
    // the indices of vcons's type cannot be unified with `plus N M` (a stuck function application)
    assertEquals(errors(vec + "f : vec A (plus N M) -> nat.\nf vnil = zero.\nf (vcons _ _) = zero.\n"), List("E0915"))
  }

  test("literal patterns for nat-like types") {
    val e = ok(nat + "fibm : nat -> int.\nfibm 0 = 0.\nfibm 1 = 1.\nfibm (suc (suc N)) = fibm N + fibm (suc N).\n")
    assertEquals(e.eval("fibm 10"), "55")
    assertEquals(e.eval("fibm 90"), "2880067194370816120")
  }

  test("functions over object code") {
    val e = ok(nat + """node : type.
                       |edge : node -> node -> rel.
                       |path : nat -> node -> node -> prop.
                       |path zero X Y = edge X Y.
                       |path (suc N) X Y = edge X Y ; path N X Y.
                       |near : node -> node -> rel.
                       |near X Y :- path 2 X Y.
                       |""".stripMargin)
    assert(e.output.contains("near X Y :- edge X Y ; edge X Y ; edge X Y."), e.output.mkString("\n"))
  }
