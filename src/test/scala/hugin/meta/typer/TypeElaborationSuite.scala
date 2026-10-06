package hugin.meta.typer

import hugin.TestSupport
import hugin.util.Diagnostic

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
