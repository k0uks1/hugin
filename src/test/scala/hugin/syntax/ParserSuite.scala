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

  test("`^` and `<` are prefix where an operand starts, binary between operands (#106)") {
    assertEquals(item("x : ^int -> ^prop = f."), "x : (⇑int -> ⇑prop) = f.")
    assertEquals(item("s = \"a\" ^ \"b\"."), "s = (\"a\" ^ \"b\").")
    assertEquals(item("e = <edge a b>."), "e = <edge a b>.")
    assertEquals(item("e = [x] <edge $x b>."), "e = [x] <edge $x b>.")
    assertEquals(item("p X :- X < 3, X > 1."), "p X :- (X < 3), (X > 1).")
    assertEquals(item("e = <(X > 1)>."), "e = <((X > 1))>.")
    // an unclosed quote is one error, E0005
    val (_, r) = parse("e = <edge a b.\nq : rel.")
    assertEquals(r.diagnostics.map(_.code.id), List("E0005"))
  }

  test("comparison operators are non-associative") {
    val (_, r) = parse("p X :- 1 < X < 3.")
    assertEquals(r.diagnostics.map(_.code).map(_.id), List("E0001"))
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
    assertEquals(r.diagnostics.map(_.code).map(_.id), List("E0001", "E0001"))
    assertEquals(p.items.collect { case d: Decl => d.name.name }, List("a", "b", "d"))
  }

  private def codes(r: Reporter): List[String] = r.diagnostics.map(_.code.id)

  test("`(e).l` is a projection") {
    assertEquals(item("p X :- (g).edge X Y."), "p X :- g.edge X Y.".replace("g.edge", "(g).edge"))
    assertEquals(item("x = (tc g).path."), "x = (tc g).path.")
  }

  test("a broken item is kept with what parsed: the error is a node of its tree") {
    val (p, r) = parse("p X :- q X, .\nr : int -> rel.")
    assertEquals(codes(r), List("E0001"))
    assertEquals(p.items.map(Printer.showItem), List("p X :- q X, <error: >.", "r : (int -> rel)."))
    assert(TreeOps.hasSyntaxErrors(p.items.head))
    assert(!TreeOps.hasSyntaxErrors(p.items(1)))
  }

  test("a declaration with a broken definition keeps its name and type") {
    val (p, r) = parse("f : int -> int = 1 + .\ng = f 2.")
    assertEquals(codes(r), List("E0001"))
    p.items.head match
      case Decl(n, Nil, tpe, None, Some(defn)) =>
        assertEquals(n.name, "f")
        assertEquals(Printer.show(tpe), "(int -> int)")
        assert(TreeOps.hasSyntaxErrors(defn))
      case other => fail(s"expected a declaration, got $other")
  }

  test("an unclosed delimiter is reported once, on its opener, with a fix; parsing continues") {
    val (p, r) = parse("p X :- q (X, r [1, 2.\ns : rel.")
    assertEquals(codes(r), List("E0005"))
    val d = r.diagnostics.head
    assertEquals(d.message, "unclosed `[`")
    assert(d.labels.exists(l => !l.primary && l.message.contains("never closed")))
    assert(d.suggestions.exists(s => s.isMachineApplicable && s.edits.map(_.replacement) == List("]")))
    assertEquals(p.items.length, 2)
  }

  test("tokens before a closing delimiter are skipped with one error") {
    val (p, r) = parse("p X :- q (X Y ] Z).\ns : rel.")
    assertEquals(codes(r), List("E0001"))
    assertEquals(r.diagnostics.head.message, "expected `)`, found `]`")
    assertEquals(p.items.length, 2)
  }

  test("a missing period is inserted before an item in column 0 and at the end of the file") {
    val (p, r) = parse("a : rel\nb : rel")
    assertEquals(codes(r), List("E0001", "E0001"))
    assertEquals(p.items.map(Printer.showItem), List("a : rel.", "b : rel."))
    assert(p.items.forall(i => !TreeOps.hasSyntaxErrors(i)))
  }

  test("a lambda's body does not start in column 0: `[x]` before the next item is a list") {
    // a missing period after a one-element list (the recovery fuzz suite's mutant of a clause)
    val (p, r) = parse("f R = [R]\n(* c *)\nsame : int -> int.\nsame R = R.")
    assertEquals(codes(r), List("E0001"))
    assertEquals(p.items.map(Printer.showItem), List("f R = [R].", "same : (int -> int).", "same R = R."))
    // a lambda whose body is on the next, indented line is still a lambda
    val (q, r2) = parse("f = [x]\n  x.")
    assertEquals(codes(r2), Nil)
    assertEquals(q.items.map(Printer.showItem), List("f = [x] x."))
  }

  test("expected sets are listed, and the start of a multi-line item is labelled") {
    val (_, r) = parse("p X\n  q ]\n  .")
    assertEquals(r.diagnostics.head.message, "expected `.`, `,` or `:-`, found `]`")
    val (_, r2) = parse("p X :-\n  q X ] .")
    assert(r2.diagnostics.head.labels.exists(_.message == "this rule starts here"))
  }

  test("specific messages for common mistakes") {
    def first(s: String) = parse(s)._2.diagnostics.head
    assertEquals(first("f :: int -> int.").message, "expected `:` in a declaration, found `::`")
    assertEquals(first("x := 5.").suggestions.head.edits.head.replacement, "")
    assertEquals(first("g : Type = { a : type, b = a }.").helps.head.take(13), "a record type")
    assertEquals(first("p X :- q (X as y).").message, "expected a variable, found `y`")
    assertEquals(first("q x : int -> rel.").suggestions.head.edits.head.replacement, "X")
    assertEquals(first("p X :- q $ .").message, "expected an expression, found `.`")
  }

  test("one error per recovery region; separators and new items resynchronise") {
    assertEquals(codes(parse("p X :- q (X, [1, (2 .")._2), List("E0005"))
    assertEquals(codes(parse("p X :- q X +, r (.")._2), List("E0001", "E0001"))
  }

  test("a module body whose items are indented ends before an item in column 0 if it is not closed") {
    val (p, r) = parse("m = {\n  a : rel.\n  a.\nb : rel.")
    assertEquals(codes(r), List("E0005"))
    assertEquals(p.items.map(Printer.showItem).last, "b : rel.")
  }

  test("the parser never gets stuck: every prefix of a program parses") {
    val text = "graph : Type = { node : type, edge : node -> node -> rel }.\n" +
      "tc (g : graph) = { path : g.node -> g.node -> rel. path X Y :- g.edge X Y. }.\n" +
      "q N :- N = count { X | p X [1, 2] }, (Y with { a = 1 }), $..xs, '( h :- b. ?- c ), f '( x ).\n%demand typed +e -t."
    for n <- 0 to text.length do parse(text.take(n))
  }
