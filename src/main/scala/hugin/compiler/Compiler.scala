package hugin.compiler

import hugin.util.*

/** The phase plan. Inner lists are fused into one traversal (dotty's MegaPhase). */
object Compiler:
  def phasePlan: List[List[Phase]] = List(
    List(hugin.syntax.ParserPhase()),
    List(ImportsPhase()),
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

  /** Runs the pipeline; returns the context. Printing goes to `out`; imports are read from disk. */
  def compile(source: SourceFile, settings: Settings, out: String => Unit): Context =
    run(Context(CompilationUnit(source), settings, Reporter()), out)

  /** Runs the pipeline on an already parsed file, loading imports with `loader` (the query database
   *  parses separately so that parsing is memoised per file). */
  def compileParsed(parsed: Parsed, settings: Settings, loader: SourceLoader, out: String => Unit): Context =
    val ctx = Context(CompilationUnit(parsed.source), settings, Reporter(), loader)
    ctx.unit.untpd = parsed.program
    parsed.diagnostics.foreach(ctx.report)
    run(ctx, out)

  private def run(ctx: Context, out: String => Unit): Context =
    given Context = ctx
    var stop = false
    for p <- phases if !stop do
      if !ctx.reporter.hasErrors || p.runsAfterErrors then
        p.run
        val names = p match
          case m: MegaPhase => m.minis.map(_.phaseName)
          case other => List(other.phaseName)
        if names.exists(ctx.settings.printAfter.contains) || ctx.settings.printAfter.contains("all") then
          out(s"(* ---------------- after ${p.phaseName} ---------------- *)")
          out(p.show)
        if ctx.settings.stopAfter.exists(names.contains) then stop = true
    ctx
