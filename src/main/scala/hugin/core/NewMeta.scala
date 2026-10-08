package hugin.core

import hugin.syntax.Trees.Item
import hugin.util.*

/** A program elaborated by the new meta level: the core state and the elaborated items. */
final class Elaborated(val core: Core, val elaborator: elab.Elaborator):
  def items: List[CoreItem] = elaborator.items.toList

  /** The elaborated program: definitions (with the inserted quotes, splices and implicit arguments) and
   *  the staged object items (for `--print-after elaborate`). */
  def render(reporter: Reporter): List[String] = Staging(core, reporter).render(items)

/** Entry point of the new meta level. */
object NewMeta:
  def elaborate(items: List[Item], reporter: Reporter): Elaborated =
    val core = Core()
    val elaborator = elab.Elaborator(core, reporter)
    elaborator.elabProgram(items)
    Elaborated(core, elaborator)

  /** The diagnostics of parsing a file in the new syntax, elaborating it and staging its object items
   *  (without the object-level phases). */
  def check(src: SourceFile): List[Diagnostic] =
    val reporter = Reporter()
    val prog = hugin.syntax.Parser.parseMeta2(src, reporter)
    if !reporter.hasErrors then
      val e = elaborate(prog.items, reporter)
      if !reporter.hasErrors then e.render(reporter)
    reporter.sorted
