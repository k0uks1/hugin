package hugin.util.diagnostics

import hugin.util.{Diagnostic, Label, Severity, Span}

/** Lint levels: flags per lint, `--deny-warnings`, and the note naming the lint. */
class LintLevelsSuite extends munit.FunSuite:
  private def warning(code: Code) = Diagnostic(Severity.Warning, code, "w", List(Label(Span.NoSpan, "", primary = true)))
  private val error = Diagnostic(Severity.Error, Code.E0501, "e")
  private val singleton = warning(Code.W0002)

  test("every lint has exactly one code, and every warning code one lint") {
    for l <- Lint.values do assertEquals(Code.values.count(_.lint.contains(l)), 1, l.name)
    assertEquals(Lint.values.map(_.code).toSet, Code.values.filter(_.level == Level.Warning).toSet)
  }

  test("lints parse by name or code") {
    assertEquals(Lint.parse("singleton_variables"), Some(Lint.SingletonVariables))
    assertEquals(Lint.parse("w0002"), Some(Lint.SingletonVariables))
    assertEquals(Lint.parse("E0501"), None)
    assertEquals(Lint.parse("nope"), None)
  }

  test("by default a lint is a warning, with a note naming it") {
    val List(d) = LintLevels()(List(singleton)): @unchecked
    assertEquals(d.severity, Severity.Warning)
    assertEquals(d.notes, List("`-W singleton_variables` is on by default"))
  }

  test("-A drops the lint, -D makes it an error; errors are untouched") {
    val allow = LintLevels().set(Lint.SingletonVariables, Level.Allow)
    assertEquals(allow(List(singleton, error)), List(error))
    val deny = LintLevels().set(Lint.SingletonVariables, Level.Error)
    val List(d, e) = deny(List(singleton, error)): @unchecked
    assertEquals(d.severity, Severity.Error)
    assertEquals(d.notes, List("`-D singleton_variables` is set on the command line"))
    assertEquals(e, error)
    assert(LintLevels.hasErrors(deny(List(singleton))))
  }

  test("the last flag for a lint wins") {
    val l = LintLevels().set(Lint.SingletonVariables, Level.Error).set(Lint.SingletonVariables, Level.Allow)
    assertEquals(l.level(Lint.SingletonVariables), Level.Allow)
  }

  test("--deny-warnings denies the lints without a flag") {
    val l = LintLevels(denyWarnings = true).set(Lint.UnusedDefinitions, Level.Warning)
    assertEquals(l.level(Lint.SingletonVariables), Level.Error)
    assertEquals(l.level(Lint.UnusedDefinitions), Level.Warning)
    assertEquals(l(List(singleton)).head.notes, List("`-D singleton_variables` is implied by `--deny-warnings`"))
  }
