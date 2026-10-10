package hugin.core

import CoreTesting.*

/** Inductive families: classification of declarations, strict positivity, predicativity, nat literals. */
class InductivesSuite extends munit.FunSuite:
  test("families and constructors are classified by their types") {
    val e = ok("""nat : Type.
                 |zero : nat.
                 |suc : nat -> nat.
                 |vec : Type -> nat -> Type.
                 |vnil : vec A zero.
                 |vcons : A -> vec A N -> vec A (suc N).
                 |opaque : nat -> int.
                 |""".stripMargin)
    assertEquals(e.global("nat").kind, GlobalKind.Inductive(List(e.elab.scope("zero"), e.elab.scope("suc"))))
    assertEquals(e.global("vec").kind, GlobalKind.Inductive(List(e.elab.scope("vnil"), e.elab.scope("vcons"))))
    assertEquals(e.global("vcons").kind, GlobalKind.Constructor(e.elab.scope("vec")))
    assertEquals(e.typeOf("vcons"), "{A : Type} -> {N : nat} -> A -> vec A N -> vec A (N + 1)")
    assertEquals(e.global("opaque").kind, GlobalKind.Postulate)
  }

  test("constructors may be declared before their family is (any order)") {
    ok("zero : nat.\nsuc : nat -> nat.\nnat : Type.\n")
  }

  test("strict positivity") {
    assertEquals(errors("bad : Type.\nmk : (bad -> int) -> bad.\n"), List("E0913"))
    assertEquals(errors("bad : Type.\nbox : Type -> Type.\nmk : box bad -> bad.\n"), List("E0913"))
    // strictly positive: to the right of arrows
    ok("nat : Type.\ntree : Type.\nleaf : tree.\nnode : (nat -> tree) -> tree.\n")
  }

  test("predicativity: constructor arguments live in the family's universe") {
    // `small` must live above the universe of its constructor's argument; then it is not in that universe
    ok("small : Type.\nmk : Type -> small.\n")
    assertEquals(errors("small : Type.\nmk : Type -> small.\nloop = mk small.\n"), List("E0904"))
  }

  test("only meta functions are defined by clauses") {
    assertEquals(errors("p : int -> rel.\np X = X.\n"), List("E0914"))
  }

  test("nat literals by expected type") {
    val e = ok("nat : Type.\nzero : nat.\nsuc : nat -> nat.\nthree : nat = 3.\nk : int = 3.\n")
    assertEquals(e.nfOf("three"), "3")
    assertEquals(e.nfOf("k"), "3")
    assertEquals(errors("nat : Type.\nzero : nat.\nsuc : nat -> nat.\nm : nat = -1.\n"), List("E0901"))
  }
