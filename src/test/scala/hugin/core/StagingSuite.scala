package hugin.core

import CoreTesting.*

/** Stage inference (quotes, splices, lifts inserted by the elaborator), cross-stage persistence of
 *  primitives, and staging of object items by evaluation. */
class StagingSuite extends munit.FunSuite:
  private val graph =
    """node : type.
      |a : node.
      |edge : node -> node -> rel.
      |""".stripMargin

  test("formula functions: object types in meta positions are lifted, bodies quoted") {
    val e = ok(graph + "loop : node -> prop = [X] edge X X.\nl : node -> rel.\nl X :- loop X.\n")
    assertEquals(e.typeOf("loop"), "⇑node -> ⇑prop")
    assertEquals(e.termOf("loop"), "[X] ⟨edge $X $X⟩")
    assert(e.output.contains("l X :- edge X X."), e.output.mkString("\n"))
  }

  test("relations as arguments of meta functions") {
    val e = ok(
      graph + "both : (node -> node -> rel) -> node -> node -> prop = [r] [x] [y] r x y, r y x.\ns : node -> node -> rel.\ns X Y :- both edge X Y.\n"
    )
    assertEquals(e.typeOf("both"), "⇑(node -> node -> rel) -> ⇑node -> ⇑node -> ⇑prop")
    assertEquals(e.termOf("both"), "[r] [x] [y] ⟨$r $x $y, $r $y $x⟩")
    assert(e.output.contains("s X Y :- edge X Y, edge Y X."), e.output.mkString("\n"))
  }

  test("records of object code: modules as arguments") {
    val e = ok(graph + """graph : Type = { node : type, edge : node -> node -> rel }.
                         |linked : (g : graph) -> g.node -> g.node -> prop = [g] [x] [y] g.edge x y.
                         |l : node -> node -> rel.
                         |l X Y :- linked { node = node, edge = edge } X Y.
                         |""".stripMargin)
    assert(e.output.contains("l X Y :- edge X Y."), e.output.mkString("\n"))
  }

  test("persistence: compile-time primitives in object code") {
    val e = ok("k : int = 6 * 7.\nq : int -> rel.\nq k.\nq $k.\nq (k + 1).\n")
    assertEquals(e.nfOf("k"), "42")
    assert(e.output.contains("q 42."), e.output.mkString("\n"))
    assert(e.output.contains("q (42 + 1)."), e.output.mkString("\n"))
  }

  test("meta int and object int: `int` in a meta position is the meta primitive, `⇑int` object code") {
    val e = ok(
      "q : int -> rel.\nsmall : ⇑int -> prop = [x] x < 10.\nlimit : int -> ⇑int -> prop = [n] [x] x < n.\nr : int -> rel.\nr X :- q X, small X, limit 5 X.\n"
    )
    assertEquals(e.typeOf("limit"), "int -> ⇑int -> ⇑prop")
    assert(e.output.contains("r X :- q X, X < 10, X < 5."), e.output.mkString("\n"))
  }

  test("object code where a compile-time value is needed is a stage error") {
    assertEquals(errors("q : int -> rel.\nlimit : int -> prop = [n] q n.\nr : int -> rel.\nr X :- limit X.\n"), List("E0902"))
  }

  test("object types computed at compile time are spliced") {
    val e = ok("name : type = string.\nexpr : type.\nref : name -> expr.\n")
    assertEquals(e.typeOf("ref"), "$name -> expr")
    assertEquals(e.termOf("name"), "⟨string⟩")
  }

  test("type families are meta functions returning object types") {
    val e = ok("list A : type.\nnil : list A.\ncons : A -> list A -> list A.\n")
    assertEquals(e.typeOf("nil"), "{A : ⇑type} -> ⇑$(list A)")
    assertEquals(e.typeOf("cons"), "{A : ⇑type} -> ⇑($A -> $(list A) -> $(list A))")
  }

  test("stuck meta code in object items is a staging error") {
    assertEquals(errors("f : int -> int.\nq : int -> rel.\nq (f 1).\n"), List("E0909"))
    assertEquals(errors("k : int = 1 / 0.\np : int -> rel.\np k.\n"), List("E0909"))
  }

  test("explicit splices and lifts") {
    val e = ok(graph + "c : ⇑node = a.\np : node -> rel.\np $c.\n")
    assertEquals(e.termOf("c"), "⟨a⟩")
    assert(e.output.contains("p a."), e.output.mkString("\n"))
    assertEquals(errors(graph + "p : node -> rel.\np X :- p $X.\n"), List("E0902"))
  }
