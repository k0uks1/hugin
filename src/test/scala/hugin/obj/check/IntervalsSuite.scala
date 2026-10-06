package hugin.obj
package check

import hugin.syntax.Literal
import hugin.util.Span
import org.scalacheck.{Gen, Prop}

/** The interval reasoning of the termination check (issue #2) is sound: whenever a valuation satisfies a
 *  body, every term's value lies in its interval and every difference in its difference interval. */
class IntervalsSuite extends munit.ScalaCheckSuite:
  private val sp = Span.NoSpan
  private val names = List("X", "Y", "Z", "W")
  private def v(n: String): Term = Term.Var(n)(sp)
  private def lit(i: Int): Term = Term.Lit(Literal.IntL(i.toLong))(sp)

  private def term(depth: Int): Gen[Term] =
    val leaf = Gen.oneOf(Gen.oneOf(names).map(v), Gen.choose(-5, 5).map(lit))
    if depth == 0 then leaf
    else
      Gen.frequency(
        3 -> leaf,
        2 -> Gen.zip(term(depth - 1), term(depth - 1)).map((a, b) => Term.Arith(ArithOp.Add, a, b)(sp)),
        2 -> Gen.zip(term(depth - 1), term(depth - 1)).map((a, b) => Term.Arith(ArithOp.Sub, a, b)(sp)),
        1 -> Gen.zip(term(depth - 1), Gen.choose(-3, 3)).map((a, l) => Term.Arith(ArithOp.Mul, a, lit(l))(sp)),
        1 -> Gen.zip(term(depth - 1), Gen.choose(1, 4)).map((a, l) => Term.Arith(ArithOp.Div, a, lit(l))(sp)),
        1 -> term(depth - 1).map(a => Term.Neg(a)(sp))
      )

  private def eval(t: Term, env: Map[String, BigInt]): BigInt = t match
    case Term.Var(n) => env(n)
    case IntLit(l) => l
    case Term.Arith(ArithOp.Add, a, b) => eval(a, env) + eval(b, env)
    case Term.Arith(ArithOp.Sub, a, b) => eval(a, env) - eval(b, env)
    case Term.Arith(ArithOp.Mul, a, b) => eval(a, env) * eval(b, env)
    case Term.Arith(ArithOp.Div, a, b) => eval(a, env) / eval(b, env) // truncating, like Prims
    case Term.Neg(a) => -eval(a, env)
    case other => throw IllegalArgumentException(other.toString)

  /** A valuation and a body of comparisons that it satisfies. */
  private val satisfied: Gen[(Map[String, BigInt], List[Formula])] =
    for
      values <- Gen.listOfN(names.length, Gen.choose(-20, 20))
      env = names.zip(values.map(BigInt(_))).toMap
      pairs <- Gen.choose(1, 6).flatMap(n => Gen.listOfN(n, Gen.zip(term(2), term(2))))
      ops <- Gen.listOfN(pairs.length, Gen.choose(0, 1))
    yield
      val body = pairs.zip(ops).map { case ((l, r), pick) =>
        val (a, b) = (eval(l, env), eval(r, env))
        val op =
          if a == b then List(CmpOp.Eq, CmpOp.Le, CmpOp.Ge)(pick)
          else if a < b then List(CmpOp.Lt, CmpOp.Le)(pick)
          else List(CmpOp.Gt, CmpOp.Ge)(pick)
        Formula.Cmp(op, l, r)(sp): Formula
      }
      (env, body)

  property("every term lies in its interval") {
    Prop.forAll(satisfied, term(2)) { case ((env, body), t) =>
      val arith = Arithmetic(body)
      val value = eval(t, env)
      val iv = arith(t)
      iv.lo.forall(_ <= value) && iv.hi.forall(_ >= value)
    }
  }

  property("every difference lies in its difference interval") {
    Prop.forAll(satisfied, term(1), term(1)) { case ((env, body), a, b) =>
      val d = Arithmetic(body).difference(a, b)
      val value = eval(a, env) - eval(b, env)
      d.lo.forall(_ <= value) && d.hi.forall(_ >= value)
    }
  }

  test("bounds propagate through equations (issue #2)") {
    // N > 1, A = N - 1  gives  A >= 1 and N - A = 1
    val body = List(
      Formula.Cmp(CmpOp.Gt, v("N"), lit(1))(sp),
      Formula.Cmp(CmpOp.Eq, v("A"), Term.Arith(ArithOp.Sub, v("N"), lit(1))(sp))(sp)
    )
    val arith = Arithmetic(body)
    assertEquals(arith(v("A")).lo, Some(BigInt(1)))
    assertEquals(arith.difference(v("N"), v("A")), Interval.point(1))
  }

  test("halving is bounded through truncating division") {
    val body = List(
      Formula.Cmp(CmpOp.Ge, v("N"), lit(3))(sp),
      Formula.Cmp(CmpOp.Eq, v("H"), Term.Arith(ArithOp.Div, v("N"), lit(2))(sp))(sp)
    )
    assertEquals(Arithmetic(body)(v("H")).lo, Some(BigInt(1)))
  }
