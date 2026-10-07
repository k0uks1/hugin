package hugin.core

import CoreTesting.*

/** Termination of meta functions: structural, lexicographic, mutual and permuted recursion are accepted;
 *  non-decreasing recursion is rejected. */
class SizeChangeSuite extends munit.FunSuite:
  private val nat = "nat : Type.\nzero : nat.\nsuc : nat -> nat.\n"

  test("structural recursion") {
    ok(nat + "double : nat -> nat.\ndouble zero = zero.\ndouble (suc N) = suc (suc (double N)).\n")
  }

  test("lexicographic: Ackermann") {
    val e = ok(nat +
      """ack : nat -> nat -> nat.
        |ack zero N = suc N.
        |ack (suc M) zero = ack M 1.
        |ack (suc M) (suc N) = ack M (ack (suc M) N).
        |""".stripMargin)
    assertEquals(e.eval("ack 2 1"), "suc (suc (suc (suc (suc zero))))")
  }

  test("mutual recursion") {
    ok(nat +
      """even : nat -> nat.
        |odd : nat -> nat.
        |even zero = 1.
        |even (suc N) = odd N.
        |odd zero = 0.
        |odd (suc N) = even N.
        |""".stripMargin)
  }

  test("permuted arguments (size-change)") {
    ok(nat + "swap : nat -> nat -> nat.\nswap zero M = M.\nswap (suc N) M = swap M N.\n")
  }

  test("non-decreasing recursion is rejected") {
    assertEquals(errors(nat + "loop : nat -> nat.\nloop N = loop N.\n"), List("E0912"))
    assertEquals(errors(nat + "grow : nat -> nat.\ngrow zero = zero.\ngrow (suc N) = grow (suc (suc N)).\n"), List("E0912"))
    assertEquals(errors(nat + "f : nat -> nat.\ng : nat -> nat.\nf N = g N.\ng N = f N.\n"), List("E0912", "E0912"))
  }

  test("the diagnostic shows the offending call") {
    val text = firstError(nat + "loop : nat -> nat.\nloop N = loop N.\n")
    assert(text.contains("cannot show that `loop` terminates"), text)
    assert(text.contains("loop N"), text)
  }
