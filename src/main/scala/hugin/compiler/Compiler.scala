package hugin.compiler

import hugin.util.*

/** The phase plan. Inner lists are fused into one traversal (dotty's MegaPhase). */
object Compiler:
  def phasePlan: List[List[Phase]] = List(
    List(hugin.syntax.ParserPhase()),
    List(hugin.meta.NamerPhase()),
    List(hugin.meta.TyperPhase()),
    List(hugin.meta.MetaEvalPhase()),
    List(hugin.meta.MonomorphizePhase()),
    List(hugin.obj.DirectivesPhase()),
    List(hugin.obj.ConstFold()),
    List(hugin.obj.ObjTyperPhase()),
    List(hugin.obj.ModingPhase()),
    List(hugin.obj.Records(), hugin.obj.Disjunctions()),
    List(hugin.obj.DemandPhase()),
    List(hugin.obj.DerivationsPhase()),
    List(hugin.obj.StratifyPhase()),
    List(hugin.obj.CompletenessPhase()),
    List(hugin.obj.TerminationPhase()),
    List(hugin.ir.LowerPhase())
  )

  def phases: List[Phase] = phasePlan.map {
    case List(p) => p
    case ms => MegaPhase(ms.map(_.asInstanceOf[MiniPhase]))
  }

  def allPhaseNames: List[String] = phasePlan.flatten.map(_.phaseName)

  /** Runs the pipeline; returns the context. Printing goes to `out`. */
  def compile(source: SourceFile, settings: Settings, out: String => Unit): Context =
    val ctx = Context(CompilationUnit(source), settings, Reporter())
    given Context = ctx
    var stop = false
    for p <- phases if !stop do
      if !ctx.reporter.hasErrors || p.runsAfterErrors then
        p.run
        val names = p match
          case m: MegaPhase => m.minis.map(_.phaseName)
          case other => List(other.phaseName)
        if names.exists(settings.printAfter.contains) || settings.printAfter.contains("all") then
          out(s"(* ---------------- after ${p.phaseName} ---------------- *)")
          out(p.show)
        if settings.stopAfter.exists(names.contains) then stop = true
    ctx
