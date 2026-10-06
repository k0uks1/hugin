package hugin.compiler

import hugin.util.*
import hugin.syntax.Program

/** The phase plan. Inner lists are fused into one traversal (dotty's MegaPhase). */
object Compiler:
  def phasePlan: List[List[Phase]] = List(
    List(hugin.syntax.ParserPhase()),
    List(hugin.meta.NamerPhase()),
    List(hugin.meta.typer.TyperPhase()),
    List(hugin.meta.MetaEvalPhase()),
    List(hugin.meta.MonomorphizePhase()),
    List(hugin.obj.typing.DirectivesPhase()),
    List(hugin.obj.typing.ConstFold()),
    List(hugin.obj.typing.ObjTyperPhase()),
    List(hugin.obj.typing.ModingPhase()),
    List(hugin.obj.transform.Records(), hugin.obj.transform.Disjunctions()),
    List(hugin.obj.transform.DemandPhase()),
    List(hugin.obj.transform.DerivationsPhase()),
    List(hugin.obj.check.StratifyPhase()),
    List(hugin.obj.check.CompletenessPhase()),
    List(hugin.obj.check.TerminationPhase()),
    List(hugin.ir.LowerPhase())
  )

  def phases: List[Phase] = phasePlan.map {
    case List(p) => p
    case ms => MegaPhase(ms.map(_.asInstanceOf[MiniPhase]))
  }

  def allPhaseNames: List[String] = phasePlan.flatten.map(_.phaseName)

  /** Runs the pipeline; returns the context. Printing goes to `out`. */
  def compile(source: SourceFile, settings: Settings, out: String => Unit): Context =
    compileParsed(source, None, settings, out)

  /** Runs the pipeline; with `parsed`, the given program and its parse diagnostics are used instead of
   *  running the parser (the query database parses separately so that parsing is memoised on its own). */
  def compileParsed(source: SourceFile, parsed: Option[(Program, List[Diagnostic])], settings: Settings, out: String => Unit): Context =
    val ctx = Context(CompilationUnit(source), settings, Reporter())
    for (program, diags) <- parsed do
      ctx.unit.untpd = program
      diags.foreach(ctx.report)
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
    ctx.unit.explanations.foreach(out)
    ctx
