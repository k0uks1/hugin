package hugin.core

import CoreTesting.*

/** Operators of the meta level bound to meta functions (#186, batch P2b): `%infix + plus.` makes `a + b`
 *  the application `plus a b`; several bindings of a symbol are chosen between by the types (E0932 if
 *  several fit, E0933 if none does); `≡` (ASCII `==`) is an operator of its own; a binding to a
 *  constructor is a pattern. */
class OperatorBindingsSuite extends munit.FunSuite:
  private val nats =
    """nat : Type.
      |zero : nat.
      |suc : nat -> nat.
      |plus : nat -> nat -> nat.
      |plus N 0 = N.
      |plus N (M + 1) = suc (plus N M).
      |times : nat -> nat -> nat.
      |times N 0 = 0.
      |times N (M + 1) = plus (times N M) N.
      |eq : {A : Type} -> A -> A -> Type.
      |refl : {A : Type} -> {x : A} -> eq x x.
      |cong : {A B : Type} -> {x y : A} -> (f : A -> B) -> eq x y -> eq (f x) (f y).
      |cong F refl = refl.
      |%infix + plus.
      |%infix * times.
      |%infix ≡ eq.
      |""".stripMargin

  test("an operator bound to a meta function is its application, with the table's precedence") {
    val e = ok(nats + "a : nat = 1 + 2 * 3.\nb : nat = (1 + 2) * 3.\n")
    assertEquals(e.termOf("a"), "plus 1 (times 2 3)")
    assertEquals(e.nfOf("a"), "7")
    assertEquals(e.nfOf("b"), "9")
  }

  test("`e + k` with a literal stays the successor, also in patterns; any other sum applies the binding") {
    val e = ok(nats + "pred : nat -> nat.\npred 0 = 0.\npred (N + 1) = N.\nf : nat -> nat -> nat.\nf N M = pred (N + 1 + M).\n")
    assertEquals(e.eval("f 2 3"), "5")
    assertEquals(e.eval("1 + 1"), "2")
  }

  test("`≡` and `==` in types bind looser than arithmetic and tighter than `->`") {
    val e = ok(
      nats +
        """zeroPlus : (n : nat) -> 0 + n ≡ n.
          |zeroPlus 0 = refl.
          |zeroPlus (N + 1) = cong suc (zeroPlus N).
          |two : 1 + 1 == 2 = refl.
          |""".stripMargin
    )
    assertEquals(e.typeOf("zeroPlus"), "(n : nat) -> eq {nat} (plus 0 n) n")
    // literals alone are integers, as without bindings: the built-in `+` of `int`
    assertEquals(e.typeOf("two"), "eq {int} (1 + 1) 2")
  }

  test("a chain of `≡` is a syntax error: the operator is not associative") {
    assertEquals(errors(nats + "x : 1 ≡ 1 ≡ 1.\n"), List("E0001"))
  }

  test("a function may be bound before its declaration, and used before it") {
    val e = ok(
      """%infix + add.
        |nat : Type.
        |zero : nat.
        |suc : nat -> nat.
        |double : nat -> nat.
        |double N = N + N.
        |add : nat -> nat -> nat.
        |add N 0 = N.
        |add N (M + 1) = suc (add N M).
        |four : nat = double 2.
        |""".stripMargin
    )
    assertEquals(e.nfOf("four"), "4")
  }

  private val two =
    nats +
      """bit : Type.
        |o : bit.
        |i : bit.
        |xor : bit -> bit -> bit.
        |xor o B = B.
        |xor i o = i.
        |xor i i = o.
        |%infix + xor.
        |""".stripMargin

  test("overloading: the binding is chosen by the expected type or by the type of an operand") {
    val e = ok(
      two +
        """a : bit = i + i.
          |b : nat = 2 + 3.
          |f : bit -> bit = [x] x + i.
          |g : nat -> nat = [x] x + x.
          |c = f o.
          |d = g 4.
          |""".stripMargin
    )
    assertEquals(e.termOf("a"), "xor i i")
    assertEquals(e.nfOf("b"), "5")
    assertEquals(e.nfOf("c"), "i")
    assertEquals(e.nfOf("d"), "8")
  }

  test("overloading inside an equation: the operand decides where the expected type is unknown") {
    val e = ok(two + "t : i + o ≡ i = refl.\nu : (n : nat) -> n + 0 ≡ n = [n] refl.\n")
    assertEquals(e.typeOf("t"), "eq {bit} (xor i o) i")
    assertEquals(e.typeOf("u"), "(n : nat) -> eq {nat} (plus n 0) n")
  }

  test("two bindings that both fit are ambiguous (E0932); none that fits is E0933 with the candidates") {
    val generic =
      """pick : {A : Type} -> A -> A -> A.
        |pick X Y = X.
        |other : {A : Type} -> A -> A -> A.
        |other X Y = Y.
        |%infix ^ pick.
        |%infix ^ other.
        |thing : Type.
        |t : thing.
        |""".stripMargin
    assertEquals(errors(generic + "x : thing = t ^ t.\n"), List("E0932"))
    val msg = firstError(nats + "flag : Type.\nyes : flag.\nx = yes + yes.\n")
    assert(msg.contains("error[E0933]"), msg)
    assert(msg.contains("`+` denotes `plus : nat -> nat -> nat`"), msg)
    // a type variable is rigid: only a binding generic at that argument fits it
    assertEquals(errors(nats + "double : {A : Type} -> A -> A.\ndouble X = X + X.\n"), List("E0933"))
    assertEquals(errors(two + "add = [x] [y] x + y.\n"), List("E0932"))
    // an integer literal next to an operand of unknown type makes it an `int`, as without bindings
    assertEquals(ok(two + "inc = [x] x + 1.\n").typeOf("inc"), "(x : int) -> int")
  }

  test("`≡` without a binding is E0933, also in object code") {
    assertEquals(errors("nat : Type.\nzero : nat.\nx : zero ≡ zero.\n"), List("E0933"))
    assertEquals(errors(nats + "p : int -> rel.\np X :- p Y, X ≡ Y.\n"), List("E0933"))
  }

  test("built-in arithmetic applies where no binding fits; object code never uses bindings") {
    val e = ok(nats + "x : int = 2 + 3.\ny : string = \"a\" ^ \"b\".\np : int -> rel.\np 1.\np Y :- p X, X < 5, Y = X + 1.\n")
    assertEquals(e.nfOf("x"), "5")
    assertEquals(e.nfOf("y"), "\"ab\"")
    assert(e.output.contains("p Y :- p X, X < 5, Y = X + 1."), e.output.mkString("\n"))
  }

  test("an operator bound to a constructor is a pattern; one bound to a function is not") {
    val e = ok(
      nats +
        """pair : Type.
          |mk : nat -> nat -> pair.
          |%infix * mk.
          |swap : pair -> pair.
          |swap (X * Y) = Y * X.
          |s = swap (1 * 2).
          |""".stripMargin
    )
    assertEquals(e.nfOf("s"), "mk 2 1")
    assertEquals(errors(nats + "f : nat -> nat.\nf (N + M) = N.\n"), List("E0915"))
  }

  test("`%infix op f.` needs a meta constant of the file with two explicit arguments (E0701)") {
    assertEquals(errors(nats + "%infix - suc.\n"), List("E0701"))
    assertEquals(errors(nats + "node : type.\nedge : node -> node -> rel.\n%infix - edge.\n"), List("E0701"))
    assertEquals(errors(nats + "%infix - nothing.\n"), List("E0101"))
  }
