package hugin.obj
package check

import hugin.TestSupport
import hugin.compiler.Settings
import hugin.syntax.Bound

/** Type-consistency violations as values (E0606): the reason and the binding atom are data. */
class BoundColumnProblemsSuite extends munit.FunSuite:
  private val prefix = """
    node : type = string.
    edge : node -> node -> int -> rel.
    source : node -> rel.
  """

  /** The violation of the last rule of `code`, checked against the components of the compiled unit. */
  private def violation(code: String): Option[BoundColumnError] =
    val c = TestSupport.compile(prefix + code, Settings(stopAfter = Some("bound-columns")))
    val p = c.unit.prog
    assert(p != null)
    val compOf = c.unit.components.zipWithIndex.flatMap((comp, i) => comp.map(_ -> i)).toMap
    val r = p.rules.last
    val h = Termination.headRel(r).get
    TypeConsistency.check(r, x => compOf.get(x).exists(compOf.get(h).contains))

  test("a wrong sign in the head names the variable, the place and the binding atom") {
    violation("""
      d : (v : node) -> (d : min int) -> rel.
      d S 0 :- source S.
      d W (C - D) :- d V D, edge V W C.
    """) match
      case Some(BoundColumnError.Inconsistent(_, Inconsistency.WrongSign(v, k, place, positive), boundBy)) =>
        assertEquals((v, k, place, positive), (VarName("D"), Bound.Min, Place.HeadColumn(Bound.Min), Bound.Min))
        assertEquals(boundBy.map(_._2), Some(Bound.Min))
      case other => fail(s"unexpected $other")
  }

  test("an equality test on a bound value is a misuse") {
    violation("""
      d : (v : node) -> (d : min int) -> rel.
      d S 0 :- source S.
      d W D :- d V D, edge V W C, D = C.
    """) match
      case Some(BoundColumnError.Inconsistent(_, Inconsistency.Misused(t, Misuse.InTest(CmpOp.Eq)), Some(_))) =>
        assertEquals(ObjPrinter.term(t), "D")
      case other => fail(s"unexpected $other")
  }

  test("a type-consistent rule has no violation") {
    assertEquals(
      violation("""
        d : (v : node) -> (d : min int) -> rel.
        d S 0 :- source S.
        d W (D + C) :- d V D, edge V W C.
      """),
      None
    )
  }
