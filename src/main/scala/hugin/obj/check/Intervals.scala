package hugin.obj
package check

import hugin.syntax.Literal

/** A closed integer interval; `None` is an infinite bound. Bounds are exact (`BigInt`): the primitive
 *  operations are undefined on overflow, so a rule whose body overflows never fires. */
final case class Interval(lo: Option[BigInt], hi: Option[BigInt]):
  def &(o: Interval): Interval = Interval(Interval.max(lo, o.lo), Interval.min(hi, o.hi))
  def +(o: Interval): Interval = Interval(for a <- lo; b <- o.lo yield a + b, for a <- hi; b <- o.hi yield a + b)
  def unary_- : Interval = Interval(hi.map(-_), lo.map(-_))
  def -(o: Interval): Interval = this + -o
  def shift(l: BigInt): Interval = Interval(lo.map(_ + l), hi.map(_ + l))

  /** Multiplication by a literal. */
  def times(l: BigInt): Interval =
    if l >= 0 then Interval(lo.map(_ * l), hi.map(_ * l)) else Interval(hi.map(_ * l), lo.map(_ * l))

  /** Truncating division by a positive literal, which is monotone. */
  def div(l: BigInt): Interval = Interval(lo.map(_ / l), hi.map(_ / l))

  /** The values `x` with `x * l` in this interval, for a positive literal `l`. */
  def unTimes(l: BigInt): Interval = Interval(lo.map(Interval.ceilDiv(_, l)), hi.map(Interval.floorDiv(_, l)))

  /** The values `x` with `x / l` (truncating) in this interval, for a positive literal `l`. */
  def unDiv(l: BigInt): Interval =
    Interval(lo.map(a => if a > 0 then a * l else a * l - l + 1), hi.map(b => if b >= 0 then b * l + l - 1 else b * l))

  def show: String = (lo, hi) match
    case (Some(a), Some(b)) if a == b => s"= $a"
    case (Some(a), Some(b)) => s"in $a..$b"
    case (Some(a), None) => s">= $a"
    case (None, Some(b)) => s"<= $b"
    case (None, None) => "unbounded"

object Interval:
  val Top: Interval = Interval(None, None)
  def point(v: BigInt): Interval = Interval(Some(v), Some(v))
  def atLeast(v: BigInt): Interval = Interval(Some(v), None)
  def atMost(v: BigInt): Interval = Interval(None, Some(v))
  private def max(a: Option[BigInt], b: Option[BigInt]) = (a ++ b).maxOption
  private def min(a: Option[BigInt], b: Option[BigInt]) = (a ++ b).minOption
  private def floorDiv(a: BigInt, b: BigInt): BigInt = if a >= 0 then a / b else -((-a + b - 1) / b)
  private def ceilDiv(a: BigInt, b: BigInt): BigInt = -floorDiv(-a, b)

/** Bounds of integer terms implied by the comparisons of a rule body (issue #2, proposal 1).
 *
 *  Every comparison `l op r` with `op` in `= < <= > >=` is a constraint; a constraint narrows the interval
 *  of each side from the other side, and narrowing an arithmetic term narrows its operands (`A = N - 1`
 *  with `N >= 2` gives `A >= 1`, and `A >= 1` gives `N >= 2`). Constraints are propagated to a fixed
 *  point, with a bounded number of rounds since cyclic constraints (`X < Y, Y < X`) narrow forever.
 *  Every step is sound: when the body holds, each term's value lies in its interval. Atoms, negations
 *  and aggregates contribute nothing; terms of other types only meet non-integer literals and stay
 *  unbounded. */
final class Bounds private (env: Map[Term, Interval]):
  /** The interval of an integer term. */
  def apply(t: Term): Interval = Bounds.eval(t, env)

object Bounds:
  private val Rounds = 16

  def of(body: List[Formula]): Bounds =
    val constraints = body.collect { case Formula.Cmp(op, l, r) => (op, l, r) }
    var env = Map.empty[Term, Interval]
    def refine(t: Term, iv: Interval): Unit =
      val old = env.getOrElse(t, Interval.Top)
      val now = old & iv
      if now != old then
        t match
          case Term.Lit(_) =>
          case _ =>
            env = env.updated(t, now)
            t match
              case Term.Arith(ArithOp.Add, x, y) =>
                refine(x, now - eval(y, env))
                refine(y, now - eval(x, env))
              case Term.Arith(ArithOp.Sub, x, y) =>
                refine(x, now + eval(y, env))
                refine(y, eval(x, env) - now)
              case Term.Arith(ArithOp.Mul, x, IntLit(l)) if l > 0 => refine(x, now.unTimes(l))
              case Term.Arith(ArithOp.Mul, IntLit(l), x) if l > 0 => refine(x, now.unTimes(l))
              case Term.Arith(ArithOp.Div, x, IntLit(l)) if l > 0 => refine(x, now.unDiv(l))
              case Term.Neg(x) => refine(x, -now)
              case _ =>
    var round = 0
    var before = env
    while round == 0 || (env != before && round < Rounds) do
      before = env
      round += 1
      for (op, l, r) <- constraints do
        val (li, ri) = (eval(l, env), eval(r, env))
        op match
          case CmpOp.Eq => refine(l, ri); refine(r, li)
          case CmpOp.Lt => refine(l, Interval(None, ri.hi.map(_ - 1))); refine(r, Interval(li.lo.map(_ + 1), None))
          case CmpOp.Le => refine(l, Interval(None, ri.hi)); refine(r, Interval(li.lo, None))
          case CmpOp.Gt => refine(l, Interval(ri.lo.map(_ + 1), None)); refine(r, Interval(None, li.hi.map(_ - 1)))
          case CmpOp.Ge => refine(l, Interval(ri.lo, None)); refine(r, Interval(None, li.hi))
          case CmpOp.Ne => // no interval information
    Bounds(env)

  private def eval(t: Term, env: Map[Term, Interval]): Interval =
    val structural = t match
      case IntLit(v) => Interval.point(v)
      case Term.Arith(ArithOp.Add, x, y) => eval(x, env) + eval(y, env)
      case Term.Arith(ArithOp.Sub, x, y) => eval(x, env) - eval(y, env)
      case Term.Arith(ArithOp.Mul, x, IntLit(l)) => eval(x, env).times(l)
      case Term.Arith(ArithOp.Mul, IntLit(l), x) => eval(x, env).times(l)
      case Term.Arith(ArithOp.Div, x, IntLit(l)) if l > 0 => eval(x, env).div(l)
      case Term.Neg(x) => -eval(x, env)
      case Term.Ascr(x, _) => eval(x, env)
      case _ => Interval.Top
    structural & env.getOrElse(t, Interval.Top)

/** An integer literal. */
object IntLit:
  def unapply(t: Term): Option[BigInt] = t match
    case Term.Lit(Literal.IntL(v)) => Some(BigInt(v))
    case _ => None
