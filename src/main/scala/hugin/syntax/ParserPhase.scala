package hugin.syntax

import hugin.compiler.*

/** Phase: lexing and parsing (Section 2). */
final class ParserPhase extends Phase:
  def phaseName = "parser"
  def description = "lex and parse into surface trees (Section 2)"
  def run(using Context): Unit =
    ctx.unit.untpd = Parser.parse(ctx.unit.source, ctx.reporter)
  override def show(using Context): String = Printer.showProgram(ctx.unit.untpd.nn)
