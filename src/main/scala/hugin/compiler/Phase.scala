package hugin.compiler

import hugin.obj.{ObjPrinter, Query, Rule}

/** A compiler phase. Phases mutate the compilation unit, as in dotty. */
abstract class Phase:
  def phaseName: String
  def description: String

  /** Whether the phase is meaningful when earlier phases reported errors. */
  def runsAfterErrors: Boolean = true
  def run(using Context): Unit

  /** Textual form of the unit after this phase (for `--print-after`). */
  def show(using Context): String = ""

/** A rule-level transformation that can be fused with others into a [[MegaPhase]]. */
abstract class MiniPhase extends Phase:
  def prepare(using Context): Unit = ()
  def transformRule(r: Rule)(using Context): List[Rule] = List(r)
  def transformQuery(q: Query)(using Context): Query = q
  def finish(using Context): Unit = ()

  def run(using Context): Unit = MegaPhase(List(this)).run

  override def show(using Context): String = ObjPrinter.program(ctx.unit.prog.nn)

/** Runs a group of mini phases in one traversal, each rule flowing through all of them. */
final class MegaPhase(val minis: List[MiniPhase]) extends Phase:
  def phaseName: String = minis.map(_.phaseName).mkString("+")
  def description: String = minis.map(_.description).mkString("; ")
  override def runsAfterErrors: Boolean = minis.forall(_.runsAfterErrors)
  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    minis.foreach(_.prepare)
    def through(r: Rule, ms: List[MiniPhase]): List[Rule] = ms match
      case Nil => List(r)
      case m :: rest => m.transformRule(r).flatMap(through(_, rest))
    p.rules = p.rules.flatMap(r => through(r, minis))
    p.queries = p.queries.map(q => minis.foldLeft(q)((q, m) => m.transformQuery(q)))
    minis.foreach(_.finish)
  override def show(using Context): String = ObjPrinter.program(ctx.unit.prog.nn)
