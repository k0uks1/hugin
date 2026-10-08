package hugin.core

import CoreTesting.*

/** Diagnostics of the new elaborator: one test per error code, checking the rendered message. */
class ElabErrorsSuite extends munit.FunSuite:
  private def assertError(code: String, program: String, fragments: String*): Unit =
    val e = elaborate(program)
    assert(e.errors.contains(code), s"expected $code, got ${e.errors}")
    val text = firstError(program)
    fragments.foreach(f => assert(text.contains(f), s"`$f` not in\n$text"))

  test("E0101 unresolved name, with a suggestion") {
    assertError("E0101", "nat : Type.\nx : natt.\n", "unresolved name `natt`", "`nat`")
  }

  test("E0102 duplicate declaration") {
    assertError("E0102", "nat : Type.\nnat : Type.\n", "`nat` is declared twice in this scope", "first declared here")
  }

  test("E0901 mismatched types") {
    assertError("E0901", "nat : Type.\nz : nat.\nx : int = z.\n", "mismatched types", "expected `int`, found `nat`")
  }

  test("E0901 notes the occurs check") {
    assertError("E0901", "bad = [x] x x.\n", "mismatched types", "occurs check")
  }

  test("E0902 stage errors in both directions") {
    assertError(
      "E0902",
      "q : int -> rel.\nscale : int -> int = [n] n * 2.\nr : int -> rel.\nr X :- q X, q (scale X).\n",
      "object code used where a compile-time value is needed"
    )
    assertError("E0902", "nat : Type.\nz : nat.\nq : int -> rel.\nq z.\n", "compile-time value used as object code")
  }

  test("E0903 cannot infer") {
    assertError("E0903", "bad = [x] x.\n", "cannot infer")
  }

  test("E0904 universe inconsistency") {
    assertError("E0904", "u : Type = Type.\nbad : u = u.\n", "universe inconsistency", "`Type : Type` is excluded")
  }

  test("E0905 not a function") {
    assertError("E0905", "limit : int = 3.\ntwice = limit 2.\n", "not a function", "is not a function type")
  }

  test("E0906 unknown field") {
    assertError("E0906", "r = { a = 1 }.\nx = r.b.\n", "no field `b`", "`a`")
  }

  test("E0907 not supported yet") {
    assertError("E0907", "m = { small : type <: int. }.\n", "refinements and families in module bodies are not supported")
  }

  test("E0908 object-level functions") {
    assertError("E0908", "r : type -> rel.\n", "cannot take object types as arguments")
    assertError(
      "E0908",
      "q : int -> rel.\nr : int -> rel.\nr X :- q X.\nf : ⇑(int -> int) = [x] x.\n",
      "object-level functions cannot be defined"
    )
  }

  test("E0909 staging failure") {
    assertError("E0909", "f : int -> int.\nq : int -> rel.\nq (f 1).\n", "cannot compute a primitive value at compile time")
  }

  test("E0910 invalid rule head") {
    assertError("E0910", "q : int -> int -> rel.\nq 1.\n", "incomplete rule head")
  }

  test("E0103 declarations that are neither relations nor constructors") {
    assertError("E0103", "limit : int.\n", "cannot classify the declaration of `limit`", "result is the base type `int`")
    assertError("E0103", "f : int -> type.\n", "a function returning `type`", "`f A : type.`")
  }

  test("E0103 `%builtin` only as the definition of a base type") {
    assertError("E0103", "num : type = %builtin integer.\n", "unknown base type `integer`")
    assertError("E0103", "n = %builtin int.\n", "only allowed as the definition of a base type")
  }

  test("E0105 a definition referring to itself") {
    assertError("E0105", "self : int = self + 1.\n", "`self` refers to itself", "while elaborating this definition")
  }

  test("E0406 a data constructor passed where a relation is expected") {
    val program =
      "shape : type.\nsquare : int -> shape.\nuse (r : shape -> shape -> rel) = { p : shape -> shape -> rel. p X Y :- r X Y. }.\nm = use square.\n"
    assertError("E0406", program, "data constructor `square` used as a relation", "expected a relation")
  }
