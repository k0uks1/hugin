package hugin.core

import StagedTesting.*

/** Module bodies, functors, signatures and their requirements, imports (reference: modules). */
class ModulesSuite extends munit.FunSuite:
  private val graph = "%use \"std/graph\".\nn : type. a : n. b : n.\nnext : n -> n -> rel.\nnext a b.\n"

  test("a functor's body is generative: each application in an item creates its own relations") {
    val p = staged(graph + "r1 = tc { node = n, edge = next }.\nr2 = tc { node = n, edge = next }.\n")
    assert(p.contains("r1.path : n -> n -> rel."), p)
    assert(p.contains("r2.path : n -> n -> rel."), p)
    assert(p.contains("r1.path X Z :- next X Y, r1.path Y Z."), p)
  }

  test("a definition evaluated once: its uses share the instance") {
    val p = staged(graph + "r = tc { node = n, edge = next }.\nq : n -> rel.\nq X :- r.path a X.\ns : n -> rel.\ns X :- r.path X b.\n")
    assertEquals(p.linesIterator.count(_.startsWith("r.path : ")), 1, p)
  }

  test("members in any order; meta definitions in bodies") {
    val p = staged("m = {\n  p : t -> rel.\n  t : type.\n  k : int = 3.\n  q : int -> rel.\n  q X :- X = k.\n}.\n")
    assert(p.contains("m.p : m.t -> rel."), p)
  }

  test("functors with implicit type parameters and formula-function arguments") {
    val p = staged(
      "item : int -> rel.\ncheap : int -> prop = [I] I < 10.\nselect (p : A -> prop) (r : A -> rel) = {\n  sel : A -> rel.\n  sel X :- r X, p X.\n}.\nb = select cheap item.\n"
    )
    assert(p.contains("b.sel X :- item X, X < 10."), p)
  }

  test("requirements of signatures are recorded at the application and checked by the object level") {
    assertEquals(
      errors(
        graph + "%open next.\ng : Type = { node : type, edge : node -> node -> rel, %complete edge }.\niso (x : g) = {\n  lonely : x.node -> rel.\n  lonely N :- x.edge N _, not x.edge _ N.\n}.\nr = iso { node = n, edge = next }.\n"
      ),
      List("E0208", "E0602")
    )
  }

  test("negation over a parameter's relation needs %complete") {
    assertEquals(
      errors(
        "g : Type = { node : type, edge : node -> node -> rel }.\niso (x : g) = {\n  lonely : x.node -> rel.\n  lonely N :- x.edge N _, not x.edge _ N.\n}.\n"
      ),
      List("E0210")
    )
  }
