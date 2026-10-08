package hugin.compiler

import hugin.TestSupport
import hugin.util.*
import hugin.util.diagnostics.{Applicability, Code, Legacy, Suggestion}

/** Machine-applicable suggestions: applying the edit makes the diagnostic go away. */
class SuggestionsSuite extends munit.FunSuite:
  private def diagnostics(code: String): List[Diagnostic] = TestSupport.compile(code).reporter.diagnostics

  /** The suggestions of the diagnostic with `code`. */
  private def suggestions(text: String, code: String): List[Suggestion] =
    val d = diagnostics(text).find(_.code.exists(_.id == code)).getOrElse(fail(s"no $code in ${diagnostics(text)}"))
    d.suggestions

  /** Applies the edits of a suggestion, from the last to the first, so that offsets stay valid. */
  private def apply(text: String, s: Suggestion): String =
    s.edits.sortBy(-_.span.start).foldLeft(text) { (t, e) =>
      assertEquals(e.span.source.path, "test.hgn")
      t.substring(0, e.span.start) + e.replacement + t.substring(e.span.end)
    }

  /** Applies the `n`-th suggestion of the diagnostic `code`; the result no longer has that diagnostic. */
  private def fix(text: String, code: String, n: Int = 0): String =
    val fixed = apply(text, suggestions(text, code)(n))
    assert(!diagnostics(fixed).exists(_.code.exists(_.id == code)), s"$code remains after the fix:\n$fixed")
    fixed

  test("a singleton variable: `_` first, or a name starting with `_`") {
    val text = "e : int -> int -> rel.\n%input e.\nsrc : int -> rel.\nsrc X :- e X Y.\n"
    assertEquals(suggestions(text, "W0002").map(_.message), List("replace `Y` with `_`", "rename `Y` to `_Y`"))
    assert(fix(text, "W0002").contains("e X _."))
    assert(fix(text, "W0002", 1).contains("e X _Y."))
  }

  test("missing labels in a body: as `_`, or ignored with `..`") {
    val text = "p : (a : int) -> (b : int) -> (c : int) -> rel.\n%input p.\nq : int -> rel.\nq X :- p { a = X }.\n"
    assert(fix(text, "E0301").contains("p { a = X, b = _, c = _ }"))
    assert(fix(text, "E0301", 1).contains("p { a = X, .. }"))
    assertEquals(diagnostics(fix(text, "E0301")).filter(_.severity == Severity.Error), Nil)
  }

  test("missing labels in a head become variables named after the labels") {
    val text = "p : (a : int) -> (b : int) -> rel.\np { a = 1 }.\n"
    assertEquals(suggestions(text, "E0301").map(s => apply(text, s)), List(text.replace("a = 1 }", "a = 1, b = B }")))
  }

  test("a functor negating over a relation parameter: add `%complete` to an inline signature") {
    val text =
      """iso (x : { node : type, edge : node -> node -> rel }) = {
        |  lonely : x.node -> rel.
        |  lonely N :- x.edge N _, not x.edge _ N.
        |}.
        |""".stripMargin
    assert(fix(text, "E0210").contains("{ node : type, edge : node -> node -> rel, %complete edge }"))
  }

  test("a functor negating over a relation parameter: add `%complete` to a named signature") {
    val text =
      """g : mod = { node : type, edge : node -> node -> rel }.
        |iso (x : g) = {
        |  lonely : x.node -> rel.
        |  lonely N :- x.edge N _, not x.edge _ N.
        |}.
        |""".stripMargin
    assertEquals(suggestions(text, "E0210").map(_.message), List("add `%complete edge`"))
    assert(fix(text, "E0210").startsWith("g : mod = { node : type, edge : node -> node -> rel, %complete edge }."))
  }

  test("a signature of the prelude is not edited") {
    val text =
      """lonely (x : graph) = {
        |  out : x.node -> rel.
        |  out N :- x.edge N _, not x.edge _ N.
        |}.
        |""".stripMargin
    val s = suggestions(text, "E0210")
    assert(s.forall(_.edits.forall(_.span.source.path.startsWith(SourceLoader.StdlibPrefix))), s)
  }

  test("an unresolved name with a similar declaration") {
    val text = "road : int -> rel.\n%input road.\nq : int -> rel.\nq X :- rod X.\n"
    assertEquals(suggestions(text, "E0101").map(_.message), List("replace with `road`"))
    assert(fix(text, "E0101").contains(":- road X."))
  }

  test("a missing period at the end of a line") {
    val text = "p : rel\nq : rel.\n"
    assertEquals(fix(text, "E0001"), "p : rel.\nq : rel.\n")
  }

  test("a missing mode: declare it before the relation, indented like it") {
    val text =
      """m : mod = { node : type, edge : node -> node -> rel, %mode edge + - }.
        |deg (x : m) = {
        |  out : x.node -> x.node -> rel.
        |  out A B :- x.edge A B.
        |}.
        |v : type.
        |f : v -> v -> rel.
        |%input f.
        |b = deg { node = v, edge = f }.
        |""".stripMargin
    assert(fix(text, "E0208").contains("%mode f + -.\nf : v -> v -> rel."))
  }

  test("a type definition that is not strict can be marked `%abbrev`") {
    val text = "t A : type = int.\n"
    assertEquals(fix(text, "E0106"), "%abbrev t A : type = int.\n")
  }

  test("generated code has no span, so no suggestion") {
    val d = Legacy.warning(Code.W0002, "x", Span.NoSpan).withSuggestion("m", Span.NoSpan, "_", Applicability.MachineApplicable)
    assertEquals(d.suggestions, Nil)
  }
