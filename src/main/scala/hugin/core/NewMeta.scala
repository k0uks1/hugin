package hugin.core

import hugin.util.*

/** Entry point of the new meta level (`hugin check --new-meta`, `hugin run --new-meta`): parses a file in
 *  the new syntax, elaborates it and stages its object items. Not yet part of the compiler pipeline. */
object NewMeta:
  final case class Result(diagnostics: List[Diagnostic], output: List[String]):
    def hasErrors: Boolean = diagnostics.exists(_.severity == Severity.Error)

  def elaborate(src: SourceFile): Result =
    val reporter = Reporter()
    val prog = hugin.syntax.Parser.parseMeta2(src, reporter)
    val core = Core()
    val elaborator = elab.Elaborator(core, reporter)
    if !reporter.hasErrors then elaborator.elabProgram(prog.items)
    val out =
      if reporter.hasErrors then Nil
      else Staging(core, reporter).render(elaborator.items.toList)
    Result(reporter.sorted, if reporter.hasErrors then Nil else out)
