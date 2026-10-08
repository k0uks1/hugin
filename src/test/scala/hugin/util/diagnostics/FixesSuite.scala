package hugin.util.diagnostics

import hugin.util.{Diagnostic, Severity, SourceFile, Span}

/** Choosing and applying machine-applicable suggestions (`hugin fix`). */
class FixesSuite extends munit.FunSuite:
  private val file = SourceFile.virtual("a.hgn", "p X :- q X Y.\n")
  private val other = SourceFile.virtual("lib.hgn", "q : rel.\n")

  private def edit(from: Int, until: Int, text: String, src: SourceFile = file) = Edit(Span(src, from, until), text)
  private def sugg(app: Applicability, edits: Edit*) = Suggestion("s", edits.toList, app)
  private def diag(ss: Suggestion*) = Diagnostic(Severity.Warning, Code.W0002, "m", suggestions = ss.toList)

  test("only machine-applicable suggestions within the file are taken") {
    val ok = sugg(Applicability.MachineApplicable, edit(11, 12, "_"))
    val guess = sugg(Applicability.MaybeIncorrect, edit(0, 1, "r"))
    val elsewhere = sugg(Applicability.MachineApplicable, edit(2, 3, "_"), edit(0, 0, "%x ", other))
    assertEquals(Fixes.applicable(List(diag(ok, guess), diag(elsewhere)), "a.hgn"), List(ok))
  }

  test("of touching suggestions the first wins") {
    val a = sugg(Applicability.MachineApplicable, edit(11, 12, "_"))
    val b = sugg(Applicability.MachineApplicable, edit(11, 12, "_Y"))
    val c = sugg(Applicability.MachineApplicable, edit(12, 12, ","))
    val d = sugg(Applicability.MachineApplicable, edit(0, 0, "% "))
    assertEquals(Fixes.applicable(List(diag(a, b), diag(c, d)), "a.hgn"), List(a, d))
  }

  test("edits apply from the last to the first, against the original offsets") {
    val text = "p X :- q X Y.\n"
    assertEquals(Fixes.apply(text, List(edit(0, 0, "%x "), edit(11, 12, "_"))), "%x p X :- q X _.\n")
  }
