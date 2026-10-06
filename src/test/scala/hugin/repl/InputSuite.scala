package hugin.repl

import Input.Status

class InputSuite extends munit.FunSuite:
  private def check(text: String, expected: Status)(using munit.Location): Unit =
    assertEquals(Input.status(text), expected, text)

  test("an item is complete at its period") {
    check("p : rel.", Status.Complete)
    check("p : rel", Status.Incomplete)
    check("path X Y :-\n  edge X Y", Status.Incomplete)
    check("path X Y :-\n  edge X Y.", Status.Complete)
  }

  test("several items on one line; the last one decides") {
    check("a : type. b : a. c : a.", Status.Complete)
    check("a : type. b :", Status.Incomplete)
  }

  test("periods inside comments do not end an item") {
    check("p X :- (* a comment. with periods. *)", Status.Incomplete)
    check("p X :- (* a comment. *) q X.", Status.Complete)
    check("p X :- q X. (* trailing. *)", Status.Complete)
  }

  test("an unterminated comment continues, also when nested") {
    check("p : rel. (* open", Status.Incomplete)
    check("(* outer (* inner *) still open.", Status.Incomplete)
    check("(* outer (* inner *) closed *)", Status.Empty)
  }

  test("periods inside strings do not end an item") {
    check("name a \"a. b.\"", Status.Incomplete)
    check("name a \"a. b.\".", Status.Complete)
  }

  test("an unterminated string is reported, not continued") {
    check("name a \"abc", Status.Complete)
  }

  test("selections and ranges are not periods") {
    check("p X :- roads.path X", Status.Incomplete)
    check("p X :- roads.path X Y.", Status.Complete)
  }

  test("brackets must be closed before the final period") {
    check("tc (g : graph) = {\n  path : g.node -> g.node -> rel.", Status.Incomplete)
    check("tc (g : graph) = {\n  path : g.node -> g.node -> rel.\n}.", Status.Complete)
    check("p X :- (q X.", Status.Incomplete)
    check("p X :- q X).", Status.Complete) // an error more input cannot fix
  }

  test("commands, blank input and queries") {
    check(":load examples/graphs.hgn", Status.Command)
    check("  :quit", Status.Command)
    check("", Status.Empty)
    check("   \n ", Status.Empty)
    check("?- path a X", Status.Incomplete)
    check("?- path a X.", Status.Complete)
  }
