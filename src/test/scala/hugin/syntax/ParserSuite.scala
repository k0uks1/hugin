package hugin.syntax

import hugin.util.*

class ParserSuite extends munit.FunSuite:
  private def parse(s: String): (Program, Reporter) =
    val r = Reporter()
    (Parser.parse(SourceFile.virtual("t", s), r), r)

  private def item(s: String): String =
    val (p, r) = parse(s)
    assert(!r.hasErrors, r.diagnostics.map(_.message).mkString("; "))
    Printer.showItem(p.items.head)

  test("arithmetic precedence and associativity (Section 2.2)") {
    assertEquals(item("p X :- X = 1 + 2 * 3 - 4."), "p X :- (X = ((1 + (2 * 3)) - 4)).")
  }

  test("arrows are right associative and labels attach to the domain") {
    assertEquals(item("c : (n : string) -> int -> rel."), "c : (n : string) -> (int -> rel).")
  }

  test("application binds tighter than operators; selection tighter than application") {
    assertEquals(item("p X :- g.edge X Y, Y < limit."), "p X :- g.edge X Y, (Y < limit).")
  }

  test("comparison operators are non-associative") {
    val (_, r) = parse("p X :- 1 < X < 3.")
    assertEquals(r.diagnostics.flatMap(_.code).map(_.id), List("E0001"))
  }

  test("braces: record type, record value, named pattern and module body") {
    assertEquals(
      item("g : Type = { node : type, edge : node -> node -> rel }."),
      "g : Type = { node : type, edge : (node -> (node -> rel)) }."
    )
    assertEquals(item("r = tc { node = city, edge = road }."), "r = tc { node = city, edge = road }.")
    assertEquals(item("b N :- abs { name = N, .. }."), "b N :- abs { name = N, .. }.")
    assert(item("m = { path : int -> rel. path 1. }.").contains("path 1."))
  }

  test("%infix operators are resolved into applications") {
    assertEquals(item("%infix left 6 plus.\nx = 1 plus 2 plus 3."), "%infix left 6 plus.")
    val (p, _) = parse("%infix left 6 plus.\nx = 1 plus 2 plus 3.")
    assertEquals(Printer.showItem(p.items(1)), "x = plus (plus 1 2) 3.")
  }

  test("negative literals") {
    assertEquals(item("p X :- X = -5."), "p X :- (X = -5).")
    assertEquals(item("p X :- X = -9223372036854775808."), "p X :- (X = -9223372036854775808).")
  }

  test("recovery: every syntax error is reported and later items are still parsed") {
    val (p, r) = parse("a : int -> rel\nb : int -> rel.\nc X :- a X,.\nd : rel.")
    assertEquals(r.diagnostics.flatMap(_.code).map(_.id), List("E0001", "E0001"))
    assertEquals(p.items.collect { case d: Decl => d.name.name }, List("a", "b", "d"))
  }
