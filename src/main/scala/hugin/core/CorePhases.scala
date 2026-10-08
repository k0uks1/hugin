package hugin.core

import hugin.compiler.*
import hugin.util.Reporter

/** Phase: elaborate the program with the new meta level (REDESIGN §6): names, types, stages, implicit
 *  arguments, totality of meta functions. */
final class ElaboratePhase extends Phase:
  def phaseName = "elaborate"
  def description = "elaborate the meta level: types, stages, implicit arguments, totality"
  def run(using Context): Unit =
    val u = ctx.unit
    if u.untpd == null then return
    val reporter = Reporter()
    u.elaborated = NewMeta.elaborate(u.untpd.nn.items, reporter)
    reporter.diagnostics.foreach(ctx.report)
  override def show(using Context): String =
    Option(ctx.unit.elaborated).fold("")(_.nn.render(Reporter()).mkString("\n"))

/** Phase: stage the object items and hand the object program over to the object level. */
final class StagePhase extends ObjProgramPhase:
  def phaseName = "stage"
  def description = "stage the object items (run the meta code they splice) and emit the object program"
  def run(using Context): Unit =
    val u = ctx.unit
    if u.elaborated == null then return
    val reporter = Reporter()
    val e = u.elaborated.nn
    u.prog = handover.Handover(e.core, reporter).program(e.items)
    reporter.diagnostics.foreach(ctx.report)
