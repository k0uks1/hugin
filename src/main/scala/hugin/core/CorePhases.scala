package hugin.core

import hugin.compiler.*
import hugin.util.Reporter

/** Phase: elaborate the program with the meta level (reference: meta/index): names, types, stages, implicit
 *  arguments, totality of meta functions; with the prelude and the imported files (loaded here, in
 *  dependency order; missing and cyclic imports are E0108). */
final class ElaboratePhase extends Phase:
  def phaseName = "elaborate"
  def description = "load the prelude and imported files; elaborate the meta level: types, stages, implicit arguments"
  def run(using Context): Unit =
    val u = ctx.unit
    if u.untpd == null then return
    val root = u.source.path
    val program = u.untpd.nn
    val graph = ctx.libraries.graph(root, program, ctx.settings.prelude)
    graph.diagnostics.foreach(ctx.report)
    u.missingImports ++= graph.missing
    graph.files.foreach(p => u.libraries(p) = Library(p))
    val result = ctx.libraries.elaborate(root, program, graph, ctx.settings.prelude)
    u.elaborated = result.elaborated
    u.index.include(result.index)
    result.diagnostics.foreach(ctx.report)

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
    val h = handover.Handover(e.core, reporter, u.index)
    u.prog = h.program(e.items)
    u.varTypes.putAll(h.varTypes)
    u.staged = (u.prog.nn.rules, u.prog.nn.queries)
    u.requirements = h.requirements
    reporter.diagnostics.foreach(ctx.report)
