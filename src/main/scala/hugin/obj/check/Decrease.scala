package hugin.obj
package check

import hugin.util.*

/** Decrease of argument values between two terms of a rule: integers by the interval reasoning of
 *  [[Arithmetic]], terms by the proper-subterm relation, and measures lexicographically. */
object Decrease:
  /** `s < b` for integers: the body implies `b - s >= 1`, or `s = x / l` with `l >= 2`, `x <= b`, `x >= 1`. */
  def numericSmaller(b: Term, s: Term, arith: Arithmetic): Option[String] =
    val d = arith.difference(b, s)
    def sh(t: Term) = ObjPrinter.term(t)
    if d.lo.exists(_ >= 1) then Some(s"`${sh(b)} - ${ObjPrinter.arg(s)}` ${d.show}")
    else
      (s :: arith.definitions(s)).collectFirst(Function.unlift {
        case q @ Term.Arith(ArithOp.Div, x, IntLit(l))
            if l >= 2 && arith.difference(b, x).lo.exists(_ >= 0) && arith(x).lo.exists(_ >= 1) =>
          Some(s"`${sh(s)}` = `${sh(q)}` < `${sh(b)}` (`${sh(x)}` >= 1)")
        case _ => None
      })

  /** `s` is a proper subterm of `b`; variables of `b` bound to patterns (`P as V`, `V = c ...`) are unfolded. */
  def structurallySmaller(b: Term, s: Term, body: List[Formula]): Option[String] =
    def defs(v: String): List[Term] =
      def inTerm(t: Term): List[Term] = t match
        case Term.As(x, `v`) => List(x)
        case Term.As(x, _) => inTerm(x)
        case Term.App(_, as) => as.flatMap(inTerm)
        case Term.Ascr(x, _) => inTerm(x)
        case _ => Nil
      body.flatMap {
        case Formula.Atom(r, as, Some(`v`)) => Term.App(r, as)(Span.NoSpan) :: as.flatMap(inTerm)
        case Formula.Atom(_, as, _) => as.flatMap(inTerm)
        case Formula.Cmp(CmpOp.Eq, Term.Var(`v`), a: Term.App) => List(a)
        case Formula.Cmp(CmpOp.Eq, a: Term.App, Term.Var(`v`)) => List(a)
        case _ => Nil
      }
    def inside(t: Term, depth: Int): Boolean = t match
      case Term.App(_, as) => as.exists(a => a == s || inside(a, depth))
      case Term.As(x, _) => inside(x, depth)
      case Term.Ascr(x, _) => inside(x, depth)
      case Term.Var(v) if depth > 0 => defs(v).exists(inside(_, depth - 1))
      case _ => false
    def unwrap(t: Term): Term = t match
      case Term.As(x, _) => unwrap(x)
      case Term.Ascr(x, _) => unwrap(x)
      case _ => t
    if inside(unwrap(b), 3) then Some(s"`${ObjPrinter.term(s)}` is a proper subterm of `${ObjPrinter.term(b)}`") else None

  /** How `small` compares to `big` (Left: the first slot that is neither equal nor smaller, or None if all
   *  are equal), or the slot that decreases with an explanation. */
  def compare(
      slots: List[Boolean],
      big: List[Term],
      small: List[Term],
      arith: Arithmetic,
      body: List[Formula]
  ): Either[Option[Int], (Int, String)] =
    val n = slots.length
    def go(i: Int, equal: List[String]): Either[Option[Int], (Int, String)] =
      if i == n then Left(None)
      else
        val (b, s) = (big(i), small(i))
        val eqWhy =
          if b == s then Some(s"`${ObjPrinter.term(s)}` unchanged")
          else if slots(i) then
            val d = arith.difference(b, s)
            if d.lo.contains(0) && d.hi.contains(0) then Some(s"`${ObjPrinter.term(s)}` = `${ObjPrinter.term(b)}`") else None
          else if body.exists {
              case Formula.Cmp(CmpOp.Eq, l, r) => (l == b && r == s) || (l == s && r == b)
              case _ => false
            }
          then Some(s"`${ObjPrinter.term(s)}` = `${ObjPrinter.term(b)}`")
          else None
        eqWhy match
          case Some(w) if n > 1 => go(i + 1, equal :+ w)
          case Some(_) => Left(None)
          case None =>
            val lt = if slots(i) then numericSmaller(b, s, arith) else structurallySmaller(b, s, body)
            lt match
              case Some(w) =>
                val prefix = if equal.isEmpty then "" else equal.mkString("", ", ", ", ")
                Right((i, prefix + w))
              case None => Left(Some(i))
    go(0, Nil)
