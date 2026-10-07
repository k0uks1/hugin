package hugin.core

import CoreTesting.*

/** Implicit arguments: implicit Π, insertion of implicit applications and lambdas, implicit binders from
 *  free variables of declarations. */
class ImplicitsSuite extends munit.FunSuite:
  private val prelude =
    """id : {A : Type} -> A -> A = [x] x.
      |const : {A B : Type} -> A -> B -> A = [x] [y] x.
      |app : {A B : Type} -> (A -> B) -> A -> B = [f] [x] f x.
      |""".stripMargin

  test("checking against an implicit Π inserts an implicit lambda") {
    val e = ok(prelude)
    assertEquals(e.typeOf("id"), "{A : Type} -> A -> A")
    assertEquals(e.termOf("id"), "[{A}] [x] x")
    assertEquals(e.termOf("const"), "[{A}] [{B}] [x] [y] x")
  }

  test("applications insert implicit arguments solved by unification") {
    val e = ok(prelude + "k = id 42.\nc = const 1 \"s\".\n")
    assertEquals(e.termOf("k"), "id {int} 42")
    assertEquals(e.termOf("c"), "const {int} {string} 1 \"s\"")
    assertEquals(e.nfOf("c"), "1")
  }

  test("higher-order: the argument's type is inferred from a function argument") {
    val e = ok(prelude + "t = app ([x : int] x + 1) 2.\n")
    assertEquals(e.termOf("t"), "app {int} {int} ([x] x + 1) 2")
    assertEquals(e.nfOf("t"), "3")
  }

  test("free uppercase variables of a declaration are implicit binders") {
    val e = ok("comp : (B -> C) -> (A -> B) -> A -> C = [f] [g] [x] f (g x).\n")
    assertEquals(e.typeOf("comp"), "{B : Type} -> {C : Type} -> {A : Type} -> (B -> C) -> (A -> B) -> A -> C")
    val e2 =
      ok("nat : Type.\nz : nat.\nflip : (A -> B -> C) -> B -> A -> C = [f] [y] [x] f x y.\npair : nat -> nat -> nat.\nq = flip pair z.\n")
    assertEquals(e2.termOf("q"), "flip {nat} {nat} {nat} pair z")
  }

  test("an implicit argument that nothing determines is an error") {
    assertEquals(errors("nat : Type.\nbad = [x] x.\n"), List("E0903"))
  }

  test("implicits through a type family") {
    val e = ok("""vec : Type -> Type.
                 |nil : vec A.
                 |len : vec A -> int.
                 |n = len (nil : vec int).
                 |""".stripMargin)
    assertEquals(e.typeOf("nil"), "{A : Type} -> vec A")
    assertEquals(e.termOf("n"), "len {int} (nil {int})")
  }
