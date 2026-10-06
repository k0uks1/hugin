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

/** A phase whose result is the object program (`unit.prog`), printed by `--print-after`. */
trait ObjProgramPhase extends Phase:
  override def show(using Context): String = ObjPrinter.program(ctx.unit.prog.nn)

/** A rule-level transformation that can be fused with others into a [[MegaPhase]]. A phase object holds
 *  no state of a run: what one traversal needs is in the [[MiniPhase.Transformer]] that `start` returns. */
abstract class MiniPhase extends ObjProgramPhase:
  /** Starts a traversal of the unit's program. */
  def start(using Context): MiniPhase.Transformer

  def run(using Context): Unit = MegaPhase(List(this)).run

object MiniPhase:
  /** One traversal of a mini phase: every rule and query flows through it, then `finish` runs. */
  trait Transformer:
    def transformRule(r: Rule)(using Context): List[Rule] = List(r)
    def transformQuery(q: Query)(using Context): Query = q
    def finish(using Context): Unit = ()

/** Runs a group of mini phases in one traversal, each rule flowing through all of them. */
final class MegaPhase(val minis: List[MiniPhase]) extends ObjProgramPhase:
  def phaseName: String = minis.map(_.phaseName).mkString("+")
  def description: String = minis.map(_.description).mkString("; ")
  override def runsAfterErrors: Boolean = minis.forall(_.runsAfterErrors)
  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val ts = minis.map(_.start)
    def through(r: Rule, ts: List[MiniPhase.Transformer]): List[Rule] = ts match
      case Nil => List(r)
      case t :: rest => t.transformRule(r).flatMap(through(_, rest))
    p.rules = p.rules.flatMap(r => through(r, ts))
    p.queries = p.queries.map(q => ts.foldLeft(q)((q, t) => t.transformQuery(q)))
    ts.foreach(_.finish)
