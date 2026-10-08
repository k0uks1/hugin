package hugin.runtime

import hugin.obj.ArithOp

/** The values `+∞` and `-∞` of integer columns (reference: object/bound-columns): the value of a bound column whose
 *  key improves without limit (Kaminski et al.'s `∞` of limit predicates, with the sign of the column's
 *  direction). Ordered `-∞ < k < +∞` for every integer `k`. */
enum Infinity:
  case Pos, Neg
  def sign: Int = if this == Pos then 1 else -1
  def negate: Infinity = if this == Pos then Neg else Pos
  def show: String = if this == Pos then "∞" else "-∞"

/** Arithmetic and comparison of integers extended with [[Infinity]]. Only reached when an operand is
 *  infinite (finite operands take the primitive operations), so the evaluator's hot path is unchanged.
 *  `∞ - ∞`, `0 · ∞` and `∞ / ∞` are undefined (`None`): a rule computing them does not fire, as on
 *  overflow; type-consistent rules never compute them. */
object ExtendedInt:
  def isInt(w: Any): Boolean = w.isInstanceOf[java.lang.Long] || w.isInstanceOf[Infinity]

  /** The sign of a finite value (as -1, 0, 1). */
  private def signum(w: Any): Int = java.lang.Long.signum(w.asInstanceOf[java.lang.Long])

  def arith(op: ArithOp, a: Any, b: Any): Option[Any] = (a, b) match
    case (x: Infinity, y: Infinity) =>
      op match
        case ArithOp.Add => Option.when(x == y)(x)
        case ArithOp.Sub => Option.when(x != y)(x)
        case ArithOp.Mul => Some(if x == y then Infinity.Pos else Infinity.Neg)
        case _ => None
    case (x: Infinity, y: java.lang.Long) =>
      op match
        case ArithOp.Add | ArithOp.Sub => Some(x)
        case ArithOp.Mul | ArithOp.Div => scaled(x, signum(y))
        case _ => None
    case (x: java.lang.Long, y: Infinity) =>
      op match
        case ArithOp.Add => Some(y)
        case ArithOp.Sub => Some(y.negate)
        case ArithOp.Mul => scaled(y, signum(x))
        case ArithOp.Div => Some(java.lang.Long.valueOf(0L))
        case _ => None
    case _ => None

  private def scaled(x: Infinity, s: Int): Option[Any] =
    if s > 0 then Some(x) else if s < 0 then Some(x.negate) else None

  def negate(a: Any): Option[Any] = a match
    case x: Infinity => Some(x.negate)
    case _ => None

  /** Compares two integers, at least one of them possibly infinite; `None` if either is not an integer. */
  def compare(a: Any, b: Any): Option[Int] = (a, b) match
    case (x: Infinity, y: Infinity) => Some(Integer.compare(x.sign, y.sign))
    case (x: Infinity, _: java.lang.Long) => Some(x.sign)
    case (_: java.lang.Long, y: Infinity) => Some(-y.sign)
    case (x: java.lang.Long, y: java.lang.Long) => Some(java.lang.Long.compare(x, y))
    case _ => None
