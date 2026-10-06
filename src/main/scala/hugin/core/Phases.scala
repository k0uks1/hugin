package hugin.core

import hugin.util.*
import hugin.syntax.Program
import hugin.meta.{MExpr, Scope}
import hugin.obj.*
import scala.collection.mutable

final case class Settings(
    color: Boolean = false,
    printAfter: Set[String] = Set.empty,
    stopAfter: Option[String] = None,
    budget: Option[Int] = None,
    facts: List[String] = Nil,
    warnings: Boolean = true,
    explainCodes: Boolean = false
)

/** Everything the compiler knows about one source program; each phase fills in its part. */
final class CompilationUnit(val source: SourceFile):
  var untpd: Program | Null = null
  var rootScope: Scope | Null = null
  /** Scopes of module bodies (keyed by identity of the surface tree). */
  val scopes: java.util.IdentityHashMap[AnyRef, Scope] = java.util.IdentityHashMap()
  var elab: MExpr | Null = null
  /** Object program after meta evaluation (may still contain families). */
  var generic: ObjProgram | Null = null
  /** The object program, transformed in place by the object-level phases. */
  var prog: ObjProgram | Null = null
  /** Typing contexts computed by `objTyper`, keyed by rule/query identity. */
  val varTypes: java.util.IdentityHashMap[AnyRef, Map[String, OType]] = java.util.IdentityHashMap()
  /** Deferred checks of signature requirements (Section 4.4), run after evaluation. */
  val deferred: mutable.ListBuffer[() => Unit] = mutable.ListBuffer.empty
  var core: hugin.runtime.CoreProgram | Null = null
  var components: List[List[RelSym]] = Nil
  var incomplete: Set[RelSym] = Set.empty
  /** Rules named by `%derivations @r`. */
  val derivationRules: mutable.Set[String] = mutable.LinkedHashSet.empty

final class Context(val unit: CompilationUnit, val settings: Settings, val reporter: Reporter):
  def report(d: Diagnostic): Unit =
    if d.severity != Severity.Warning || settings.warnings then reporter.report(d)
  def error(code: String, msg: String, span: Span, label: String = ""): Unit =
    report(Diagnostic.error(code, msg, span, label))

def ctx(using c: Context): Context = c

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
