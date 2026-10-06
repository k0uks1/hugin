package hugin.util

class UtilSuite extends munit.FunSuite:
  test("Tarjan returns components in dependency order") {
    val succ = Map(1 -> List(2), 2 -> List(3), 3 -> List(2), 4 -> List(1))
    val comps = Tarjan.components(List(4, 1, 2, 3), (n: Int) => succ.getOrElse(n, Nil)).map(_.toSet)
    assertEquals(comps, List(Set(2, 3), Set(1), Set(4)))
  }

  test("source positions are 0-based internally and code-point based") {
    val src = SourceFile.virtual("t", "ab\n😀x")
    assertEquals(src.lineOf(4), 1)
    assertEquals(src.columnOf(5), 1) // the emoji is one column
  }

  test("diagnostics render rustc-style with labels on one row") {
    val src = SourceFile.virtual("f.hgn", "p X Y :- q X.\n")
    val d = Diagnostic.error("E0501", "rule is not range-restricted", Span(src, 4, 5), "`Y` not bound")
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
    val d = Diagnostic.error("E0001", "x", Span.NoSpan)
    r.report(d); r.report(d)
    r.report(Diagnostic.warning("W0001", "y", Span.NoSpan))
    assertEquals((r.errorCount, r.warningCount), (1, 1))
  }
