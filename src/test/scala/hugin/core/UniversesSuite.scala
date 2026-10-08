package hugin.core

import CoreTesting.*

/** Universes: `type` (object types), `Type` with inferred cumulative levels, no `Type : Type`. */
class UniversesSuite extends munit.FunSuite:
  test("Type is in a higher Type; levels are inferred") {
    val e = ok("t : Type = Type.\nnat : Type.\nn : t = nat.\n")
    assertEquals(e.typeOf("t"), "Type₁")
    assertEquals(e.typeOf("n"), "t")
  }

  test("cumulativity: a type of Type₀ is also a type of Type₁") {
    ok("nat : Type.\nf : Type -> Type = [x] x.\ng = f nat.\nh = f (Type -> Type).\n")
  }

  test("Type : Type is rejected") {
    assertEquals(errors("u : Type = Type.\nbad : u = u.\n"), List("E0904"))
  }

  test("a meta solved by a type must respect its universe") {
    // `id {Type} …` forces the level of id's implicit above the level of Type
    ok("id : {A : Type} -> A -> A = [x] x.\nnat : Type.\nt = id Type.\nu = id nat.\n")
    // well-typed by cumulativity: the inner id is used at a smaller universe (contravariant domain)
    ok("id : {A : Type} -> A -> A = [x] x.\nfine = id (id : {A : Type} -> A -> A).\n")
    // g's implicit ranges over u = Type_b, and u itself is not in Type_b
    assertEquals(errors("u : Type = Type.\ng : {A : u} -> A -> A = [x] x.\nbad = g u.\n"), List("E0904"))
  }

  test("signatures of object components live in Type₀") {
    val e = ok("graph : Type = { node : type, edge : node -> node -> rel }.\nsig : Type = { t : Type }.\n")
    assertEquals(e.typeOf("graph"), "Type")
    assertEquals(e.typeOf("sig"), "Type₁")
  }

  test("object types and meta types: classification of declarations") {
    val e = ok("""expr : type.
                 |nat : Type.
                 |ref : string -> expr.
                 |edge : expr -> expr -> rel.
                 |size : nat -> int.
                 |list A : type.
                 |""".stripMargin)
    assertEquals(e.global("expr").stage, Stage.S0)
    assertEquals(e.global("ref").stage, Stage.S0)
    assertEquals(e.global("edge").stage, Stage.S0)
    assertEquals(e.global("nat").stage, Stage.S1)
    assertEquals(e.global("size").stage, Stage.S1)
    assertEquals(e.typeOf("size"), "nat -> int")
    assertEquals(e.typeOf("list"), "(A : ⇑type) -> ⇑type")
  }
