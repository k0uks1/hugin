package hugin.core

import org.scalacheck.{Gen, Prop}

/** Shared data declarations (issue #80; reference: meta/families, shared data): the invariant
 *  `reflect (T.reify v) ≡ T.lift v` (the term data a value reifies to describes exactly the object code it
 *  lifts to), checked differentially on random values of nested, parameterised and mutually recursive
 *  shared types; and the derived functions are ordinary meta functions. */
class SharedDataSuite extends munit.ScalaCheckSuite:
  private val decls =
    """tree A : data.
      |leaf : A -> tree A.
      |node : (label : string) -> (kids : list (tree A)) -> tree A.
      |stmt : data.
      |skip : stmt.
      |when : cond -> stmt -> stmt.
      |cond : data.
      |always : cond.
      |nested : list stmt -> cond.
      |""".stripMargin

  private val int: Gen[String] = Gen.choose(-5, 20).map(n => if n < 0 then s"($n)" else n.toString)
  private val float: Gen[String] = Gen.choose(0, 40).map(n => s"${n / 4}.${(n % 4) * 25}")
  private val string: Gen[String] = Gen.oneOf("\"\"", "\"a\"", "\"b c\"", "\"x\\\"y\"")

  private def list(elem: Gen[String]): Gen[String] = Gen.choose(0, 3).flatMap(n => Gen.listOfN(n, elem)).map(_.mkString("[", ", ", "]"))
  private def option(elem: Gen[String]): Gen[String] = Gen.oneOf(Gen.const("none"), elem.map(v => s"(some $v)"))
  private def tree(depth: Int, elem: Gen[String]): Gen[String] =
    if depth == 0 then elem.map(v => s"(leaf $v)")
    else Gen.oneOf(elem.map(v => s"(leaf $v)"), Gen.zip(string, list(tree(depth - 1, elem))).map((l, ks) => s"(node $l $ks)"))
  private def stmt(depth: Int): Gen[String] =
    if depth == 0 then Gen.const("skip")
    else Gen.oneOf(Gen.const("skip"), Gen.zip(cond(depth - 1), stmt(depth - 1)).map((c, s) => s"(when $c $s)"))
  private def cond(depth: Int): Gen[String] =
    if depth == 0 then Gen.const("always") else Gen.oneOf(Gen.const("always"), list(stmt(depth - 1)).map(ss => s"(nested $ss)"))

  /** A type and a random value of it. */
  private val typed: Gen[(String, String)] = Gen.oneOf(
    tree(3, option(int)).map(("tree (option int)", _)),
    list(list(string)).map(("list (list string)", _)),
    option(tree(2, float)).map(("option (tree float)", _)),
    stmt(4).map(("stmt", _)),
    list(option(int)).map(("list (option int)", _))
  )

  private def program(ty: String, value: String, use: String): String =
    s"${decls}held : $ty -> rel.\nv : $ty = $value.\n$use\n"

  property("reflect (T.reify v) is T.lift v: the reflected fact is the lifted one") {
    Prop.forAll(typed) { (ty, value) =>
      val lifted = StagedTesting.staged(program(ty, value, "held v."))
      val reflected = StagedTesting.staged(program(ty, value, "$'{ held $v. }."))
      assertEquals(reflected, lifted, s"$ty = $value")
      true
    }
  }

  test("the lifted and the reflected value run to the same facts") {
    val code = program("tree (option int)", "node \"r\" [leaf (some 1), leaf none]", "held v.\nagain : tree (option int) -> rel.\n$'{ again $v. }.\nsame : int -> rel.\nsame 1 :- held X, again X.\n%output same.")
    assertEquals(StagedTesting.run(code), Right(List("same 1.")))
  }

  test("the derived functions are meta functions of the declared types, usable by name") {
    val code = decls + "x : ⇑(tree int) = tree.lift ([y : int] y) (leaf 3).\nheld : tree int -> rel.\nheld $x.\nr : term = tree.reify tint (leaf 4).\n%output held."
    assertEquals(StagedTesting.run(code), Right(List("held (leaf 3).")))
  }

  test("violations of the restrictions are errors of their own") {
    assertEquals(StagedTesting.errors("t : data.\nc : (int -> int) -> t."), List("E0920"))
    assertEquals(StagedTesting.errors("t A : data.\nc : t int."), List("E0921"))
    assertEquals(StagedTesting.errors("t : data.\nc : t.\no : type.\no <: t."), List("E0922"))
    assertEquals(StagedTesting.errors("c : option string."), List("E0923"))
  }
