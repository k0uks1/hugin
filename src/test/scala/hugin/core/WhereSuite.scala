package hugin.core

import CoreTesting.*

/** `where` blocks: local definitions, local functions (lambda-lifted, with coverage and termination),
 *  irrefutable pattern bindings, scoping and layout. */
class WhereSuite extends munit.FunSuite:
  private val nat =
    """nat : Type.
      |zero : nat.
      |suc : nat -> nat.
      |pair : Type -> Type -> Type.
      |mk : A -> B -> pair A B.
      |""".stripMargin

  test("simple local definitions see the pattern variables and each other, in order") {
    val e = ok(nat + """shape : Type.
                       |rect : int -> int -> shape.
                       |area : shape -> int.
                       |area (rect W H) = w * h
                       |  where w = W + 1.
                       |        h = w + H.
                       |""".stripMargin)
    assertEquals(e.eval("area (rect 2 3)"), "18")
  }

  test("irrefutable pattern bindings (the designer's fibPair)") {
    val e = ok(nat + """fibPair : nat -> pair int int.
                       |fibPair zero = mk 0 1.
                       |fibPair (suc N) = mk b (a + b)
                       |  where mk a b = fibPair N.
                       |first : pair int int -> int.
                       |first (mk X _) = X.
                       |""".stripMargin)
    assertEquals(e.eval("first (fibPair 10)"), "55")
  }

  test("refutable pattern bindings are rejected by coverage") {
    val code = nat + """opt : Type.
                       |none : opt.
                       |some : int -> opt.
                       |get : opt -> int.
                       |get O = x
                       |  where some x = O.
                       |""".stripMargin
    assertEquals(errors(code), List("E0911"))
  }

  test("local functions by clauses, recursive, using the outer pattern variables") {
    val e = ok(nat + """addTo : int -> nat -> int.
                       |addTo K M = go M
                       |  where go : nat -> int.
                       |        go zero = K.
                       |        go (suc N) = go N + 1.
                       |""".stripMargin)
    assertEquals(e.eval("addTo 40 2"), "42")
  }

  test("local functions are checked for coverage and termination") {
    assertEquals(errors(nat + "f : nat -> int.\nf M = g M\n  where g : nat -> int.\n        g zero = 0.\n"), List("E0911"))
    assertEquals(errors(nat + "f : nat -> int.\nf M = g M\n  where g : nat -> int.\n        g N = g N.\n"), List("E0912"))
  }

  test("layout: the block ends at the next item at column 0") {
    val e = ok(nat + """two : int -> int.
                       |two X = y
                       |  where y = X * 2.
                       |three : int = two 1 + 1.
                       |""".stripMargin)
    assertEquals(e.nfOf("three"), "3")
  }

  test("the right-hand side of the outer function's recursion may be in a where block") {
    val e = ok(nat + """countDown : nat -> int.
                       |countDown zero = 0.
                       |countDown (suc N) = r + 1
                       |  where r = countDown N.
                       |""".stripMargin)
    assertEquals(e.eval("countDown 5"), "5")
  }
