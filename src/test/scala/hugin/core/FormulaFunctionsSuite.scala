package hugin.core

import StagedTesting.*

/** Formula functions defined by clauses, hygiene, `%mode` on formula functions. */
class FormulaFunctionsSuite extends munit.FunSuite:
  test("clauses define a disjunction of their bodies with the parameters equated to the arguments") {
    assertEquals(
      run(
        "n : int -> rel. n 1. n 2. n 3.\neven_odd : int -> prop.\neven_odd X :- X = 2.\neven_odd X :- X = 3.\np : int -> rel.\np X :- n X, even_odd X.\n%output p.\n"
      ),
      Right(List("p 2.", "p 3."))
    )
  }

  test("hygiene: the variables of a clause are fresh at each application") {
    val out = run(
      "e : int -> int -> rel. e 1 2. e 3 4.\nlinked : int -> prop.\nlinked X :- e X Y.\nq : int -> int -> rel.\nq X Y :- linked X, linked Y.\n%output q.\n"
    )
    assertEquals(out.map(_.length), Right(4), out.toString)
  }

  test("a formula function without clauses is false (W0005)") {
    assertEquals(errors("never : int -> prop.\nr : int -> rel.\nr X :- X = 1, never X.\n"), Nil)
  }

  test("%mode on a formula function checks its body's binding order (E0501)") {
    assertEquals(errors("f : int -> int -> prop.\n%mode f - +.\nf X Y :- Y = X + 2.\n"), List("E0501"))
  }
