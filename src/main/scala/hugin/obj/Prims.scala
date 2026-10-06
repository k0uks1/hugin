package hugin.obj

import hugin.syntax.Literal
import hugin.syntax.Literal.*

/** Shared primitive semantics ⟦⊕⟧ used at both levels (Section 3.3). `None` = undefined. */
object Prims:
  def arith(op: ArithOp, a: Literal, b: Literal): Option[Literal] = (op, a, b) match
    case (ArithOp.Add, IntL(x), IntL(y)) => exact(Math.addExact(x, y))
    case (ArithOp.Sub, IntL(x), IntL(y)) => exact(Math.subtractExact(x, y))
    case (ArithOp.Mul, IntL(x), IntL(y)) => exact(Math.multiplyExact(x, y))
    case (ArithOp.Div, IntL(x), IntL(y)) =>
      if y == 0 || (x == Long.MinValue && y == -1) then None else Some(IntL(x / y))
    case (ArithOp.Add, FloatL(x), FloatL(y)) => Some(FloatL(x + y))
    case (ArithOp.Sub, FloatL(x), FloatL(y)) => Some(FloatL(x - y))
    case (ArithOp.Mul, FloatL(x), FloatL(y)) => Some(FloatL(x * y))
    case (ArithOp.Div, FloatL(x), FloatL(y)) => if y == 0.0 then None else Some(FloatL(x / y))
    case (ArithOp.Concat, StrL(x), StrL(y)) => Some(StrL(x + y))
    case _ => None

  def neg(a: Literal): Option[Literal] = a match
    case IntL(x) => if x == Long.MinValue then None else Some(IntL(-x))
    case FloatL(x) => Some(FloatL(-x))
    case _ => None

  private def exact(f: => Long): Option[Literal] =
    try Some(IntL(f))
    catch case _: ArithmeticException => None

  /** Strings compare lexicographically by code point; ints and floats numerically. */
  def compare(a: Literal, b: Literal): Option[Int] = (a, b) match
    case (IntL(x), IntL(y)) => Some(java.lang.Long.compare(x, y))
    case (FloatL(x), FloatL(y)) => Some(java.lang.Double.compare(x, y))
    case (StrL(x), StrL(y)) => Some(compareCodePoints(x, y))
    case _ => None

  def compareCodePoints(x: String, y: String): Int =
    var i = 0
    var j = 0
    while i < x.length && j < y.length do
      val a = x.codePointAt(i)
      val b = y.codePointAt(j)
      if a != b then return Integer.compare(a, b)
      i += Character.charCount(a)
      j += Character.charCount(b)
    Integer.compare(x.length - i, y.length - j).sign

  def cmp(op: CmpOp, a: Literal, b: Literal): Boolean =
    op match
      case CmpOp.Eq => a == b
      case CmpOp.Ne => a != b
      case _ =>
        compare(a, b) match
          case None => false
          case Some(c) =>
            op match
              case CmpOp.Lt => c < 0
              case CmpOp.Le => c <= 0
              case CmpOp.Gt => c > 0
              case CmpOp.Ge => c >= 0
              case _ => false
