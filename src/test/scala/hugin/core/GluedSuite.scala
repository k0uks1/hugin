package hugin.core

import CoreTesting.*

/** Glued evaluation (issue #66): definitions stay folded in printed types, implicit arguments and meta
 *  solutions, while evaluation, comparison and staging see their values. */
class GluedSuite extends munit.FunSuite:
  private val vecs =
    """nat : Type.
      |zero : nat.
      |suc : nat -> nat.
      |vec : Type -> nat -> Type.
      |vnil : vec A zero.
      |vcons : A -> vec A N -> vec A (suc N).
      |two : nat = suc (suc zero).
      |vec2 : Type = vec int two.
      |ident : {A : Type} -> A -> A = [x] x.
      |len : vec A N -> nat.
      |len vnil = zero.
      |len (vcons _ Xs) = suc (len Xs).
      |v : vec2 = vcons 1 (vcons 2 vnil).
      |""".stripMargin

  test("an inferred type and an implicit argument keep the definition folded") {
    val e = ok(vecs + "w = ident v.\n")
    assertEquals(e.typeOf("w"), "vec2")
    assertEquals(e.termOf("w"), "ident {vec2} v")
  }

  test("a meta solved inside an unfolded type keeps its own definitions folded") {
    val e = ok(vecs + "l = len v.\n")
    assertEquals(e.termOf("l"), "len {int} {two} v")
    assertEquals(e.nfOf("l"), "suc (suc zero)")
  }

  test("conversion and evaluation see through definitions") {
    val e = ok(vecs + "u : vec int (suc (suc zero)) = v.\nn : nat = len u.\n")
    assertEquals(e.nfOf("n"), "suc (suc zero)")
    assertEquals(e.eval("len v"), "suc (suc zero)")
  }

  test("a mismatch names the types as written") {
    val text = firstError(vecs + "bad : vec2 = vcons 1 vnil.\n")
    assert(text.contains("expected `vec2`, found `vec int (suc zero)`"), text)
  }

  test("types that look the same folded are shown unfolded") {
    val text = firstError(vecs + "h : vec2 -> nat = [x] zero.\ng (vec2 : Type) (x : vec2) : nat = h x.\n")
    assert(text.contains("expected `vec int (suc (suc zero))`, found `vec2`"), text)
  }

  test("a signature is shown by its name, and its fields by the note") {
    val text = firstError("point : Type = { x : int, y : int }.\norigin : point = { x = 0, y = 0 }.\nz = origin.z.\n")
    assert(text.contains("`point` has the fields `x`, `y`"), text)
  }

  test("a meta equated with a definition of a function is solved eta-short") {
    val e = ok("inc (n : int) : int = n + 1.\napp : {A B : Type} -> (A -> B) -> A -> B = [f] [x] f x.\nt = app inc 2.\n")
    assertEquals(e.termOf("t"), "app {int} {int} inc 2")
    assertEquals(e.nfOf("t"), "3")
  }

  test("compile-time arithmetic and persistence compute on the values of definitions") {
    val e = ok("k : int = 6 * 7.\nm : int = k + 1.\nq : int -> rel.\nq m.\n")
    assertEquals(e.nfOf("m"), "43")
    assert(e.output.exists(_.contains("q 43.")), e.output.mkString("\n"))
  }

  test("an object type definition stays folded when spliced, and stages to its value") {
    val e = ok("name : type = string.\nperson : (n : name) -> rel.\nperson \"ann\".\n")
    assertEquals(e.typeOf("person"), "(n : $name) -> rel")
    assert(e.output.exists(_.contains("person \"ann\".")), e.output.mkString("\n"))
  }

  test("a folded definition in a solution whose spine is out of scope is unfolded") {
    // ?m is solved with `k x` where `k = [a] [b] a` drops `b`: the folded form mentions `y`, which is not in
    // ?m's scope, the unfolded value does not
    val e = ok(
      """nat : Type.
        |zero : nat.
        |k : nat -> nat -> nat = [a] [b] a.
        |eqn : nat -> nat -> Type.
        |refl : eqn N N.
        |f : (x : nat) -> (y : nat) -> eqn (k x y) x = [x] [y] refl.
        |""".stripMargin
    )
    assertEquals(e.errors, Nil)
  }

  test("a type former is never unfolded: a definition of one is compared by its arguments") {
    // as the prelude's `quoted`: a family without definition; `qi` is a definition of one of its types
    val text = firstError("wrap : ⇑type -> Type.\nqi : Type = wrap int.\na : qi.\nb : wrap string = a.\n")
    assert(text.contains("expected `wrap ⟨string⟩`, found `qi`"), text)
    ok("wrap : ⇑type -> Type.\nqi : Type = wrap int.\na : qi.\nb : wrap int = a.\n")
  }
