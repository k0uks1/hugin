package hugin.core

import CoreTesting.*
import hugin.util.*

/** Issue #195: index unification, splitting and coverage evaluate to weak-head form on demand, and meta
 *  evaluation stops when its cancellation answers yes. Budgets are counted in polls of the cancellation
 *  (a fixed number of evaluation steps each), never in time. */
class WeakHeadSuite extends munit.FunSuite:
  private val nat =
    """nat : Type.
      |zero : nat.
      |suc : nat -> nat.
      |""".stripMargin

  /** The mutant of `tests/neg/cov_undecided.hgn` that MutationFuzzSuite found: `same n 0` became `same n
   *  9223372036854775807`, and normalising `double n` took 2^63 steps. */
  private val huge = nat +
    """double : nat -> nat.
      |double 0 = 0.
      |double (N + 1) = double N + 2.
      |vec : Type -> nat -> Type.
      |vnil : vec A 0.
      |vcons : A -> vec A N -> vec A (N + 1).
      |same : nat -> nat -> Type.
      |refl : same N N.
      |empty : {n : nat} -> vec int (double n) -> same n 9223372036854775807 -> int.
      |empty vnil refl = 0.
      |""".stripMargin

  /** A loop of `n` steps that no native operation shortcuts. */
  private val loop = nat +
    """tally : nat -> nat -> nat.
      |tally 0 A = A.
      |tally (K + 1) A = tally K (A + 1).
      |""".stripMargin

  /** A cancellation that answers yes from its `after`-th poll on, counting its polls. */
  private final class AfterPolls(after: Int) extends Cancellation:
    var polls = 0
    def cancelled(): Boolean =
      polls += 1
      polls >= after

  /** Elaborates `code` (as [[CoreTesting.elaborate]]) with `cancellation` asked by its core. */
  private def elaborateWith(code: String, cancellation: Cancellation): (List[Diagnostic], Core) =
    val reporter = Reporter()
    val prog = hugin.syntax.Parser.parse(SourceFile.virtual("test.hgn", code), reporter)
    val core = Core()
    core.cancellation = cancellation
    hugin.core.elab.Elaborator(core, reporter).elabProgram(prog.items)
    (reporter.sorted, core)

  /** The message of the `InterruptedException` that `body` ends with (not `NonFatal`, so not `intercept`). */
  private def stopped(body: => Unit): Option[String] =
    try
      body
      None
    catch case e: InterruptedException => Some(e.getMessage)

  test("a huge numeral in an index is refuted after one step of the function applied to it") {
    // within 1000 polls (about a million steps; normalising took 2^63)
    val budget = AfterPolls(1000)
    val (diagnostics, _) = elaborateWith(huge, budget)
    val errors = diagnostics.filter(_.severity == Severity.Error)
    assertEquals(errors.map(_.code.id), List("E0915"))
    val shown = DiagnosticRenderer(color = false).render(errors.head)
    // the index is shown as it is: its normal form is too expensive to compute
    assert(shown.contains("its index `0` conflicts with `double 9223372036854775807`"), shown)
    assert(budget.polls < 1000, s"${budget.polls} polls")
  }

  test("an index whose normal form is cheap is shown normalised") {
    val e = elaborate(huge.replace("9223372036854775807", "5"))
    assertEquals(e.errors, List("E0915"))
    val shown = DiagnosticRenderer(color = false).render(e.diagnostics.find(_.severity == Severity.Error).get)
    assert(shown.contains("its index `0` conflicts with `10`"), shown)
  }

  test("weak-head forms: one step of a function, arguments delayed; the normal form is unchanged") {
    val e = elaborate(huge.replace("9223372036854775807", "5"))
    val core = e.core
    val double = e.elab.scope("double")
    val fam = e.elab.scope("nat")
    val delayed = core.appWeak(Val.Rigid(Head.Glob(double), Nil), Val.Nat(fam, 5), Icit.Expl)
    assertEquals(delayed, Val.Rigid(Head.Glob(double), List(Elim.EApp(Val.Nat(fam, 5), Icit.Expl))))
    core.whnf(delayed) match
      case Val.NatAdd(`fam`, Val.Rigid(Head.Glob(`double`), List(Elim.EApp(Val.Nat(_, n), _))), k) =>
        assertEquals((n, k), (BigInt(4), BigInt(2)))
      case other => fail(s"not one step of double: $other")
    assertEquals(core.quote(0, delayed), Tm.Nat(fam, 10))
    assert(core.sameWeak(0, delayed, Val.Nat(fam, 10)))
    assert(!core.sameWeak(0, delayed, Val.Nat(fam, 9)))
    assert(!core.sameWeak(0, delayed, Val.Nat(fam, 0)))
  }

  test("meta evaluation stops at the poll where the cancellation answers yes") {
    val e = ok(loop)
    val flag = AfterPolls(5)
    e.core.cancellation = flag
    assertEquals(stopped(e.eval("tally 100000000 0")), Some("evaluation cancelled"))
    assertEquals(flag.polls, 5)
    // the core evaluates again once the cancellation answers no
    e.core.cancellation = () => false
    assertEquals(e.eval("tally 3 4"), "7")
  }

  test("weak-head evaluation polls the cancellation too") {
    val e = ok(loop)
    val core = e.core
    val tally = e.elab.scope("tally")
    val fam = e.elab.scope("nat")
    val flag = AfterPolls(3)
    core.cancellation = flag
    val big = Val.Nat(fam, BigInt(10).pow(12))
    val call = Val.Rigid(Head.Glob(tally), List(Elim.EApp(Val.Nat(fam, 0), Icit.Expl), Elim.EApp(big, Icit.Expl)))
    assertEquals(stopped(core.whnf(call)), Some("evaluation cancelled"))
    assertEquals(flag.polls, 3)
  }

  test("by default, an interrupt of the evaluating thread cancels meta evaluation, and is cleared") {
    val e = ok(loop)
    Thread.currentThread.interrupt()
    assertEquals(stopped(e.eval("tally 100000000 0")), Some("evaluation cancelled"))
    assert(!Thread.interrupted())
  }

  test("a budget of polls ends an evaluation that exceeds it, and nothing else") {
    val e = ok(loop)
    val core = e.core
    val tally = e.elab.scope("tally")
    val fam = e.elab.scope("nat")
    def call(n: BigInt) =
      core.app(core.app(Val.Rigid(Head.Glob(tally), Nil), Val.Nat(fam, n), Icit.Expl), Val.Nat(fam, 0), Icit.Expl)
    assertEquals(core.withinPolls(10)(call(BigInt(10).pow(9))), None)
    assertEquals(core.withinPolls(10)(call(3)), Some(Val.Nat(fam, 3)))
  }
