package hugin.meta.typer

import hugin.TestSupport
import hugin.meta.MExpr
import hugin.obj.*
import hugin.syntax.Literal
import hugin.util.{Diagnostic, Origin, Span}

/** How meta and object types are shown in the typer's diagnostics. */
class TypeElaborationSuite extends munit.FunSuite:
  private def mismatch(code: String): Diagnostic =
    TestSupport.compile(code).reporter.diagnostics.find(_.code.contains("E0203")).getOrElse(fail("no E0203"))

  test("a Π domain is parenthesized: the arrow is right-associative") {
    val d = mismatch("""
      inc (x : int) : int = x + 1.
      hof (g : (int -> int) -> int) : int = g inc.
      bad = hof inc.
    """)
    assertEquals(d.labels.map(_.message), List("expected `(int -> int) -> int`"))
    assertEquals(d.notes, List("found `(x : int) -> int`", "parameter: expected `int`, found `int -> int`"))
  }

  test("a Π codomain is not parenthesized") {
    val d = mismatch("""
      k (x : int) (y : int) : int = x.
      app (g : int -> int -> int) : int = g 1 2.
      bad = app 3.
    """)
    assertEquals(d.labels.map(_.message), List("expected `int -> int -> int`"))
  }

  test("object types with splices: the meta printer's `~(...)`, or the caller's rendering, structurally") {
    val list = TypeSym("list", TypeKind.Open, Span.NoSpan, Origin.Source)
    val t = OType.Con(list, List(OType.Splice(MExpr.Lit(Literal.StrL("~(")))))
    assertEquals(t.show, "list ~(\"~(\")")
    assertEquals(OType.show(t, m => s"(${MExpr.show(m)})"), "list (\"~(\")")
  }

  test("a column type mentioning a module's abstract type is shown by its path") {
    val d = mismatch("""
      g : mod = { node : type, edge : list node -> rel }.
      city : type.
      use (h : list city -> rel) = h.
      f (y : g) = use y.edge.
    """)
    assertEquals(d.notes.last, "column 1 has type `list y.node` but `list city` is expected (relation types are invariant)")
  }
