package hugin.compiler

import hugin.util.*

/** The state threaded through all phases: the unit, the settings and the diagnostics reporter. */
final class Context(val unit: CompilationUnit, val settings: Settings, val reporter: Reporter):
  def report(d: Diagnostic): Unit =
    if d.severity != Severity.Warning || settings.warnings then reporter.report(d)
  def error(code: String, msg: String, span: Span, label: String = ""): Unit =
    report(Diagnostic.error(code, msg, span, label))

def ctx(using c: Context): Context = c
