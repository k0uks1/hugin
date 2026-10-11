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
    assertEquals(e.eval("ack 2 1"), "5")
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

  // Calls behind other names: the call graph follows them as evaluation does (issue #66, Batch 0). Each
  // path has a non-decreasing call (rejected; it used to be accepted and overflow the stack when used)
  // and a decreasing one (accepted).
  private def throughPath(defs: String, call: String => String): Unit =
    val looping = nat + "f : nat -> nat.\n" + defs + "f zero = zero.\nf (suc N) = " + call("(suc N)") + ".\n"
    val decreasing = nat + "f : nat -> nat.\n" + defs + "f zero = zero.\nf (suc N) = " + call("N") + ".\n"
    assertEquals(errors(looping), List("E0912"), looping)
    ok(decreasing)

  test("calls through a definition") {
    throughPath("g : nat -> nat = [x] f x.\n", a => s"g $a")
  }

  test("calls through a definition inside a definition") {
    throughPath("g1 : nat -> nat = [x] f x.\ng : nat -> nat = [x] g1 x.\n", a => s"g $a")
  }

  test("calls through a partial application stored in a definition") {
    throughPath("g : nat -> nat = f.\n", a => s"g $a")
    throughPath("k : nat -> nat -> nat = [y] [x] f x.\ng : nat -> nat = k zero.\n", a => s"g $a")
  }

  test("calls through a field of a record of functions") {
    throughPath("ops : { step : nat -> nat } = { step = [x] f x }.\n", a => s"ops.step $a")
  }

  test("calls through a member of a module") {
    throughPath("m = {\n  h : nat -> nat = [x] f x.\n}.\n", a => s"m.h $a")
  }

  test("calls through a member that calls another member") {
    throughPath("m = {\n  k : nat -> nat = [y] f y.\n  h : nat -> nat = [x] k x.\n}.\n", a => s"m.h $a")
  }

  test("calls through a functor application") {
    throughPath("mk (n : nat) = {\n  h : nat -> nat = [x] f x.\n}.\n", a => s"(mk zero).h $a")
    throughPath("mk (n : nat) = {\n  h : nat -> nat = [x] f x.\n}.\ninst = mk zero.\n", a => s"inst.h $a")
  }

  test("calls in the solution of an implicit argument") {
    val code = nat + """eqn : nat -> nat -> Type.
      |refl : eqn N N.
      |k : {n : nat} -> eqn n n -> nat = [e] zero.
      |w : (n : nat) -> eqn n n = [n] refl.
      |f : nat -> nat.
      |f zero = zero.
      |f (suc N) = k (w (f (suc N))).
      |""".stripMargin
    val text = firstError(code)
    assert(text.contains("cannot show that `f` terminates"), text)
    assert(text.contains("in this clause: `f (N + 1)`"), text)
  }

  test("a definition passed as a value calls with unknown arguments, as the function itself does") {
    val apply = "apply : (nat -> nat) -> nat -> nat = [k] [x] k x.\n"
    assertEquals(errors(nat + "f : nat -> nat.\n" + apply + "f zero = zero.\nf (suc N) = apply f N.\n"), List("E0912"))
    assertEquals(
      errors(nat + "f : nat -> nat.\ng : nat -> nat = [x] f x.\n" + apply + "f zero = zero.\nf (suc N) = apply g N.\n"),
      List("E0912")
    )
  }
