package hugin

import hugin.util.{Diagnostic, Label, Severity, Span}
import hugin.util.diagnostics.Code

/** Diagnostics built from strings, for tests of the renderers and the reporter (the compiler reports
 *  typed problems). */
object TestDiagnostics:
  def error(code: Code, message: String, span: Span, label: String = ""): Diagnostic =
    Diagnostic(Severity.Error, code, message, List(Label(span, label, primary = true)))

  def warning(code: Code, message: String, span: Span, label: String = ""): Diagnostic =
    Diagnostic(Severity.Warning, code, message, List(Label(span, label, primary = true)))
