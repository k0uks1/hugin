package hugin.core

import CoreTesting.*

/** The basics of proofs (#186, batch P2): a polymorphic identity family, implicit arguments by name and
 *  implicit patterns, opaque definitions and functions, and the conflict rule of index unification for
 *  distinct atoms. */
class ProofBasicsSuite extends munit.FunSuite:
  private val eqs =
    """nat : Type.
      |zero : nat.
      |suc : nat -> nat.
      |eq : {A : Type} -> A -> A -> Type.
      |refl : {A : Type} -> {x : A} -> eq x x.
      |trans : {A : Type} -> {x y z : A} -> eq x y -> eq y z -> eq x z.
      |trans refl Q = Q.
      |""".stripMargin

  test("an implicit argument by name inserts the implicit arguments before it and checks the one named") {
    val e = ok(eqs + "t : eq 1 1 = trans {y := 1} refl refl.\n")
    assertEquals(e.termOf("t"), "trans {int} {1} {1} {1} (refl {int} {1}) (refl {int} {1})")
  }

  test("implicit arguments by name in sequence, and a type argument of a polymorphic family") {
    val e = ok(eqs + "t : eq 1 1 = trans {x := 1} {y := 1} refl refl.\nu : eq {A := Type} nat nat = refl.\n")
    assertEquals(e.termOf("t"), "trans {int} {1} {1} {1} (refl {int} {1}) (refl {int} {1})")
    assertEquals(e.typeOf("u"), "eq {Type} nat nat")
  }

  test("an implicit argument that is not before the next explicit one is E0926") {
    assertEquals(errors(eqs + "t : eq 1 1 = trans refl {y := 1} refl.\n"), List("E0926"))
    assertEquals(errors(eqs + "t : eq 1 1 = trans {q := 1} refl refl.\n"), List("E0926"))
  }

  test("implicit patterns bind the function's and a constructor's implicit arguments") {
    val e = ok(
      """nat : Type.
        |zero : nat.
        |suc : nat -> nat.
        |vec : Type -> nat -> Type.
        |vnil : vec A 0.
        |vcons : A -> vec A N -> vec A (N + 1).
        |len : {A : Type} -> {n : nat} -> vec A n -> nat.
        |len {n := N} V = N.
        |tl : {A : Type} -> {n : nat} -> vec A n -> nat.
        |tl vnil = 0.
        |tl (vcons {N := K} X XS) = K.
        |a = len (vcons 1 (vcons 2 vnil)).
        |b = tl (vcons 1 (vcons 2 vnil)).
        |""".stripMargin
    )
    assertEquals(e.nfOf("a"), "2")
    assertEquals(e.nfOf("b"), "1")
  }

  test("an opaque definition keeps its term, is not evaluated, and does not unfold") {
    val program =
      """nat : Type.
        |zero : nat.
        |suc : nat -> nat.
        |fib : nat -> nat.
        |fib 0 = 0.
        |fib 1 = 1.
        |fib (N + 2) = plus (fib N) (fib (N + 1)).
        |plus : nat -> nat -> nat.
        |plus N 0 = N.
        |plus N (M + 1) = suc (plus N M).
        |big : nat = fib 18.
        |""".stripMargin
    // the clause steps of evaluating the definition, eagerly without `%opaque`, not at all with it
    val before = Matching.clauseSteps
    ok(program)
    val eager = Matching.clauseSteps - before
    val middle = Matching.clauseSteps
    val e = ok(program + "%opaque big.\n")
    val opaque = Matching.clauseSteps - middle
    assert(eager > opaque + 1000, s"evaluated eagerly: $eager steps without %opaque, $opaque with it")
    e.global("big").kind match
      case GlobalKind.Opaque(Some(tm), None) => assertEquals(e.core.showTm(Nil, tm), "fib 18")
      case k => fail(s"not opaque: $k")
    assertEquals(e.eval("big"), "big")
  }

  test("an opaque function is checked, keeps its case tree, and its applications do not reduce") {
    val nat = "nat : Type.\nzero : nat.\nsuc : nat -> nat.\n"
    val e = ok(nat + "double : nat -> nat.\ndouble 0 = 0.\ndouble (N + 1) = double N + 2.\n%opaque double.\n")
    assert(e.global("double").kind.isInstanceOf[GlobalKind.Opaque])
    assertEquals(e.eval("double 2"), "double 2")
    assertEquals(errors(nat + "double : nat -> nat.\ndouble 0 = 0.\n%opaque double.\n"), List("E0911"))
  }

  test("distinct atoms conflict in index unification: absurd clauses on equations of atoms") {
    ok(eqs + "a : eq 1 2 -> nat.\na ().\nb : eq \"x\" \"y\" -> nat.\nb ().\n")
    // symbols, with the prelude (quotes)
    val syms = "%use \"std/eq\".\nr = %import \"std/reflect\".\na, b : type.\n"
    assertEquals(StagedTesting.errors(syms + "c : eq {A := r.sym} '( a ) '( b ) -> nat.\nc ().\n"), Nil)
    assertEquals(StagedTesting.errors(syms + "c : eq {A := r.sym} '( a ) '( a ) -> nat.\nc ().\n"), List("E0915"))
    // equal atoms do not conflict
    assertEquals(errors(eqs + "a : eq 1 1 -> nat.\na ().\n"), List("E0915"))
  }
