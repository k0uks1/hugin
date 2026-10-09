package hugin.core

import StagedTesting.*

/** Families as memoised meta functions (reference: meta/families): instances per normalised arguments, generic rules
 *  staged at the instances used, polymorphic recursion. */
class FamiliesSuite extends munit.FunSuite:
  test("an instance per family and normalised arguments, named after them") {
    val p = staged("w : list string -> rel.\nw (cons \"a\" nil).\nv : list string -> rel.\nv nil.\n")
    assertEquals(p.linesIterator.count(_.startsWith("list[string] : type")), 1, p)
    assert(p.contains("cons[string] : string -> list[string] -> list[string]."), p)
  }

  test("generic rules are staged at the instances used, also through other instances") {
    val p = staged("%use \"std/list\".\nw : list string -> rel.\nw (cons \"a\" nil).\n?- w L, len L N.\n")
    assert(p.contains("len[string] (cons[string] X L) M :- cons[string] X L, len[string] L N, M = N + 1."), p)
    assert(!p.contains("len[int]"), p)
  }

  test("struct families: a type family in types, a constructor with implicit arguments in terms") {
    assertEquals(
      run("pair A B : type = { fst : A, snd : B }.\np : pair int string -> rel.\np (pair 1 \"x\").\n?- p X.\n"),
      Right(List("?- p X.", "X = pair 1 \"x\"."))
    )
  }

  test("polymorphic recursion is rejected") {
    assertEquals(
      errors("box A : type.\nput : A -> box A.\nnest : A -> rel.\nnest 1.\nnest (put X) :- nest X.\nnest X :- nest (put X).\n?- nest 1.\n"),
      List("E0205")
    )
  }
