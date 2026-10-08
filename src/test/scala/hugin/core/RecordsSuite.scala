package hugin.core

import CoreTesting.*

/** Records: dependent record types, record values, projections, record coercion (width and depth). */
class RecordsSuite extends munit.FunSuite:
  test("signatures and modules as record types and values") {
    val e = ok("""expr : type.
                 |edge : expr -> expr -> rel.
                 |graph : Type = { node : type, edge : node -> node -> rel }.
                 |g : graph = { node = expr, edge = edge }.
                 |e = g.edge.
                 |""".stripMargin)
    assertEquals(e.termOf("g"), "{ node = ⟨expr⟩, edge = ⟨edge⟩ }")
    assertEquals(e.typeOf("e"), "⇑(expr -> expr -> rel)")
    assertEquals(e.nfOf("e"), "⟨edge⟩")
  }

  test("dependent fields") {
    val e = ok("""nat : Type.
                 |z : nat.
                 |pointed : Type₁ = { t : Type, x : t }.
                 |""".stripMargin.replace("Type₁", "Type") + "p : pointed = { t = nat, x = z }.\nq = p.x.\n")
    assertEquals(e.typeOf("q"), "nat")
    assertEquals(e.nfOf("q"), "z")
    assertEquals(errors("nat : Type.\nz : nat.\npointed : Type = { t : Type, x : t }.\np : pointed = { t = nat, x = 1 }.\n"), List("E0901"))
  }

  test("record coercion: extra fields are dropped, fields are coerced") {
    val e = ok("r = { a = 1, b = \"s\" }.\ns : { a : int } = r.\n")
    assertEquals(e.termOf("s"), "{ a = r.a }")
    assertEquals(e.nfOf("s"), "{ a = 1 }")
  }

  test("missing and unknown fields") {
    assertEquals(errors("s : { a : int, b : int } = { a = 1 }.\n"), List("E0204"))
    assertEquals(errors("s : { a : int } = { a = 1, c = 2 }.\n"), List("E0906"))
    assertEquals(errors("r = { a = 1 }.\nx = r.b.\n"), List("E0906"))
    assertEquals(errors("r = { a = 1, a = 2 }.\n"), List("E0307"))
  }

  test("projection of object facts by column label") {
    val e = ok("""item : (name : string) -> (price : int) -> rel.
                 |cheap : item -> prop = [I] I.price < 10.
                 |""".stripMargin)
    assertEquals(e.termOf("cheap"), "[I] ⟨$I.price < 10⟩")
  }
