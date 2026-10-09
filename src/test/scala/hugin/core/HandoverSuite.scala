package hugin.core

import hugin.TestSupport
import hugin.compiler.Settings
import hugin.obj.ObjPrinter

/** The handover of staged object items to the object level (`core/handover`): the object program the
 *  `stage` phase emits, for each object form; and object typing deferred to the object typer. */
class HandoverSuite extends munit.FunSuite:
  private def staged(code: String): String =
    val c = TestSupport.compile(code, Settings(stopAfter = Some("stage")))
    assert(!c.reporter.hasErrors, c.reporter.diagnostics.map(_.message).mkString("\n"))
    ObjPrinter.program(c.unit.prog.nn)

  private def errors(code: String): List[String] =
    TestSupport.errorCodes(TestSupport.compile(code, Settings()))

  private val shop =
    """item : type = { name : string, price : int }.
      |cheap : string -> rel.
      |""".stripMargin

  test("declarations: open types, refinements, relations, constructors, structs, edges") {
    val p = staged("""age : type <: int.
                     |person : type.
                     |student : (name : string) -> (years : age) -> person.
                     |teacher : (name : string) -> rel.
                     |teacher <: person.
                     |""".stripMargin)
    assert(p.contains("age : type <: int."), p)
    assert(p.contains("student : (name : string) -> (years : age) -> person."), p)
    assert(p.contains("teacher <: person."), p)
  }

  test("named patterns, projections, updates and wildcards") {
    val p = staged(
      shop + "cheap N :- item { name = N, .. }, item N P, P < 10.\nup : item -> rel.\nseen : item -> rel.\nup (I with { price = 1 }) :- seen I, I.price > 5.\n"
    )
    assert(p.contains("cheap N :- item N _, item N P, P < 10."), p)
    assert(p.contains("up (I with { price = 1 }) :- seen I, I.price > 5."), p)
  }

  test("aggregates, disjunction, negation, `as` and ascriptions") {
    val p = staged(
      shop + "n : int -> rel.\nn C :- C = count { N | item N _ ; cheap N }.\nm : string -> rel.\nm N :- (item N _ as I), not cheap N, item N (P : int), P > 0, I.price > 0.\n"
    )
    assert(p.contains("n C :- C = count { N | (item N _ ; cheap N) }."), p)
    assert(p.contains("m N :- (item N _ as I), not (cheap N), item N (P : int), P > 0, I.price > 0."), p)
  }

  test("compile-time arithmetic of meta primitives is persisted; object arithmetic is kept") {
    val p = staged("k : int = 6 * 7.\nq : int -> rel.\nq (k + 1).\nr : int -> rel.\nr X :- q Y, X = Y + k.\n")
    assert(p.contains("q 43."), p)
    assert(p.contains("r X :- q Y, X = Y + 42."), p)
  }

  test("object declarations may refer to each other in cycles") {
    val p = staged("abs : (body : term) -> rel.\nvar : (name : string) -> rel.\nterm : type = var | abs.\n")
    assert(p.contains("abs : (body : var | abs) -> rel."), p)
  }

  test("forward references to constructors; cycles through constructors are predeclared (#86)") {
    // a forward reference is resolved by retrying the item after the declaration
    val fwd = staged("uses : (x : c) -> rel.\nt : type.\nc : (v : int) -> t.\n")
    assert(fwd.contains("uses : (x : c) -> rel."), fwd)
    // a cycle needs the constructor predeclared (its result type is an open type of the module), in
    // either order of the declarations
    val cycle = "neg : (e : small) -> expr.\nlit : (v : int) -> expr.\nsmall : type = lit | neg.\n"
    for code <- List("expr : type.\n" + cycle, cycle + "expr : type.\n") do
      val p = staged(code)
      assert(p.contains("neg : (e : lit | neg) -> expr."), p)
    assertEquals(errors("expr : type.\n" + cycle + "lit 1.\nneg (lit 1).\n"), Nil)
    // the result of a predeclared constructor must be an open type: a struct is not
    assertEquals(errors("s : type = { a : int }.\nk : (e : u) -> s.\nu : type = k.\n").nonEmpty, true)
  }

  test("object typing is the object typer's: subtyping is not rejected by the core, type errors come from it") {
    assertEquals(errors("a : type.\nb : type.\nx : a.\nr : b -> rel.\nr x.\n"), List("E0402"))
    assertEquals(errors("age : type <: int.\nr : age -> rel.\nr 30.\n"), Nil)
  }

  test("constructors are relations; named-pattern errors") {
    assertEquals(errors("t : type.\nc : int -> t.\nr : rel.\nr :- c 1.\n"), Nil)
    assertEquals(errors(shop + "cheap N :- item { name = N }.\n"), List("E0301"))
    assertEquals(errors(shop + "cheap N :- item { nam = N, .. }.\n"), List("E0306"))
  }
