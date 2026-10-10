package hugin.obj
package check

import hugin.TestSupport
import hugin.compiler.Settings

/** The termination check's verdicts as values (docs/DIAGNOSTICS.md §3.11, structural tests): the problems
 *  carry their reasons as data, independently of the wording pinned by the golden tests. */
class TerminationProblemsSuite extends munit.FunSuite:
  /** The verdict of every recursive component, by the names of its relations. */
  private def verdicts(code: String): Map[List[String], Verdict] =
    val c = TestSupport.compile(code, Settings(stopAfter = Some("termination")))
    Termination.verdicts(c.unit).map((comp, v) => comp.map(_.name) -> v).toMap

  private def rejected(code: String, comp: String*): TerminationError =
    verdicts(code)(comp.toList) match
      case Verdict.Rejected(r) => r.error
      case other => fail(s"expected a rejection of ${comp.mkString(", ")}, got $other")

  /** The only rejection of the program. */
  private def rejection(code: String): Option[TerminationError] =
    verdicts(code).values.collectFirst { case Verdict.Rejected(r) => r.error }

  private def show(t: Term): String = ObjPrinter.term(t)

  test("a component without constructive rules is finite") {
    assertEquals(verdicts("p : int -> rel. p 1. p X :- p X.")(List("p")), Verdict.Finite)
  }

  test("a decrease bounded below is accepted by descent along derivations") {
    verdicts("n : int -> rel. n 5. n A :- n N, N > 0, A = N - 1.")(List("n")) match
      case Verdict.Accepted(how, _) => assert(how.contains("descent"), how)
      case other => fail(s"accepted expected, got $other")
  }

  test("E0603: an unbounded decrease names the invention, the cycle, the failed directions and the missing guard") {
    rejected("need : int -> rel. need 5. need A :- need N, A = N - 1.", "need") match
      case TerminationError.NoArgument(comp, invention, cycle, asserted, descent, induction, guard, measurable) =>
        assertEquals(comp.map(_.name), List("need"))
        invention match
          case Invention.ComputedByEquation(v, eq) =>
            assertEquals(v, VarName("A"))
            assertEquals(ObjPrinter.formula(eq), "A = N - 1")
          case other => fail(s"unexpected invention $other")
        assertEquals(cycle.map(_.map(_.name)), Some(List("need", "need")))
        assertEquals(asserted, None)
        descent match
          case DescentFailure.NoDescent(from, to, rules) =>
            assertEquals((from.name, to.name, rules.length), ("need", "need", 1))
        assertEquals(induction, None)
        assertEquals(guard.map(g => (show(g.head), show(g.premise), g.up)), Some(("A", "N", false)))
        assertEquals(measurable.map(_.name), Some("need"))
      case other => fail(s"unexpected $other")
  }

  test("E0603: an unanchored structural measure is guarded induction's reason") {
    val code = """
      nat : type. z : nat. s : nat -> nat.
      grow : nat -> rel.
      grow z.
      grow (s N) :- grow N.
    """
    rejected(code, "grow") match
      case p: TerminationError.NoArgument =>
        assertEquals(p.invention.getClass.getSimpleName, "HeadConstructs")
        p.induction match
          case Some(a: TerminationError.NoAnchor) =>
            assertEquals((a.measure.rel.name, a.measure.positions, a.measure.slots), ("grow", List(0), List(false)))
            assertEquals(show(a.head), "s N")
            assert(a.isAnchor)
          case other => fail(s"unexpected induction failure $other")
        assertEquals(p.guard, None)
      case other => fail(s"unexpected $other")
  }

  test("E0604: a declared measure that does not decrease names the slot and the compared terms") {
    val code = """
      list A : type.
      nil : list A.
      cons : A -> list A -> list A.
      len : list A -> int -> rel.
      %terminates L (len L _).
      len nil 0.
      len (cons X L) M :- cons X L, len (cons X L) N, M = N + 1.
      nums : list int -> rel.
      nums (cons 1 nil).
      ?- nums L, len L N.
    """
    rejection(code) match
      case Some(p: TerminationError.NoDecrease) =>
        assertEquals(p.roles, Roles.CallAndHead)
        assertEquals((p.big.map(show), p.small.map(show)), (List("cons[int] X L"), List("cons[int] X L")))
        assertEquals(p.slot, None)
        assertEquals(p.measure.slots, List(false))
        assert(p.directive.isDefined)
      case other => fail(s"unexpected $other")
  }

  test("E0604: measures of different lengths in one component") {
    val code = """
      ev : int -> int -> rel.
      od : int -> int -> rel.
      %terminates (N, K) (ev N K).
      %terminates N (od N _).
      ev 0 0.
      od N K :- ev M K, M < 9, N = M + 1.
      ev N K :- od M K, M < 9, N = M + 1.
    """
    rejected(code, "ev", "od") match
      case p: TerminationError.MeasureLengths =>
        assertEquals((p.rel.name, p.length, p.first.name, p.firstLength), ("od", 1, "ev", 2))
        assert(p.firstAt.isDefined)
      case other => fail(s"unexpected $other")
  }

  test("E0603: a decreasing demanded integer without a lower bound (the demand relation does not descend)") {
    val code = """
      fib : (n : int) -> (f : int) -> rel.
      %demand fib +n -f.
      %terminates n fib.
      fib 0 0.
      fib 1 1.
      fib N F :- N <> 0, N <> 1, A = N - 1, B = N - 2, fib A FA, fib B FB, F = FA + FB.
    """
    rejection(code) match
      case Some(p: TerminationError.NoArgument) =>
        assertEquals(p.comp.map(_.name), List("fib.check"))
      case other => fail(s"unexpected $other")
  }
