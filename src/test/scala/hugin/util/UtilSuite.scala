package hugin.util

import hugin.TestDiagnostics
import hugin.util.diagnostics.Code

class UtilSuite extends munit.FunSuite:
  test("strongly connected components come in dependency order, ties in input order") {
    val succ = Map(1 -> List(2), 2 -> List(3), 3 -> List(2), 4 -> List(1), 5 -> List(5))
    val comps = Graphs.components(List(4, 5, 1, 2, 3), (n: Int) => succ.getOrElse(n, Nil))
    assertEquals(comps, List(List(5), List(2, 3), List(1), List(4)))
  }

  test("shortest paths over parallel edges") {
    val edges = List(("a", "b", 1), ("a", "b", 2), ("b", "c", 3), ("a", "c", 4), ("c", "a", 5))
    val path = Graphs.shortestPath(edges, (e: (String, String, Int)) => e._1, (e: (String, String, Int)) => e._2, "b", "a")
    assertEquals(path.map(_._3), List(3, 5))
    assertEquals(Graphs.shortestPath(edges, (e: (String, String, Int)) => e._1, (e: (String, String, Int)) => e._2, "a", "x"), Nil)
  }

  test("source positions are 0-based internally and code-point based") {
    val src = SourceFile.virtual("t", "ab\n😀x")
    assertEquals(src.lineOf(4), 1)
    assertEquals(src.columnOf(5), 1) // the emoji is one column
  }

  test("diagnostics render rustc-style with labels on one row") {
    val src = SourceFile.virtual("f.hgn", "p X Y :- q X.\n")
    val d = TestDiagnostics.error(Code.E0501, "rule is not range-restricted", Span(src, 4, 5), "`Y` not bound")
      .withLabel(Span(src, 0, 1), "head")
      .withHelp("bind it")
    val text = DiagnosticRenderer(color = false).render(d)
    assertNoDiff(
      text,
      """error[E0501]: rule is not range-restricted
        | --> f.hgn:1:5
        |  |
        |1 | p X Y :- q X.
        |  | -   ^ `Y` not bound
        |  | head
        |  |
        |  = help: bind it
        |""".stripMargin
    )
  }

  test("the reporter deduplicates identical diagnostics and counts severities") {
    val r = Reporter()
    val d = TestDiagnostics.error(Code.E0001, "x", Span.NoSpan)
    r.report(d); r.report(d)
    r.report(TestDiagnostics.warning(Code.W0001, "y", Span.NoSpan))
    assertEquals((r.errorCount, r.warningCount), (1, 1))
  }

  test("spans in a slice resolve to the file it is placed in; equality ignores the placement") {
    val slice = SourceFile.slice("f", "q X :- p X.")
    val sp = Span(slice, 2, 3)
    assertEquals((sp.source eq slice, sp.start, sp.text), (true, 2, "X"))
    val v1 = SourceFile.virtual("f", "p 1.\nq X :- p X.\n")
    slice.place(v1, 5)
    assertEquals((sp.source eq v1, sp.start, sp.end, sp.show, sp.text), (true, 7, 8, "f:2:3", "X"))
    val hash = sp.hashCode
    val v2 = SourceFile.virtual("f", "p 1.\n\n  q X :- p X.\n")
    slice.place(v2, 8)
    assertEquals((sp.source eq v2, sp.start, sp.show), (true, 10, "f:3:5"))
    assertEquals((sp, sp.hashCode), (Span(slice, 2, 3), hash))
    assertEquals(sp.to(Span(slice, 9, 10)), Span(slice, 2, 10))
    assertEquals(sp.in(v1), sp) // already in the current text
    intercept[IllegalArgumentException](slice.place(v2, 0)) // the slice does not lie there
  }
