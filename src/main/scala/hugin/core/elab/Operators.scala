package hugin.core
package elab

import hugin.obj.{ArithOp, BaseType, CmpOp}
import hugin.syntax.Tree
import hugin.syntax.Trees.*
import hugin.util.*

/** Operators: arithmetic (object code at stage 0, computed at compile time at stage 1), comparisons and
 *  the connectives of object formulas (`,` `;` `not`). A literal operand takes the type (and stage) of the
 *  other operand. */
trait Operators:
  self: Elaborator =>
  import core.*

  val arithOps: Map[String, ArithOp] =
    Map("+" -> ArithOp.Add, "-" -> ArithOp.Sub, "*" -> ArithOp.Mul, "/" -> ArithOp.Div, "^" -> ArithOp.Concat)
  private val cmpOps: Map[String, CmpOp] =
    Map("=" -> CmpOp.Eq, "<>" -> CmpOp.Ne, "<" -> CmpOp.Lt, "<=" -> CmpOp.Le, ">" -> CmpOp.Gt, ">=" -> CmpOp.Ge)

  private def isLit(t: Tree): Boolean = t match
    case Lit(_) => true
    case Parens(i) => isLit(i)
    case Neg(i) => isLit(i)
    case _ => false

  /** The operand to infer first (not a literal, if possible) and the other one; `true` if swapped. */
  private def order(l: Tree, r: Tree): (Tree, Tree, Boolean) =
    if isLit(l) && !isLit(r) then (r, l, true) else (l, r, false)

  def inferInfix(c: Cxt, op: String, l: Tree, r: Tree, span: Span, st: Option[Stage]): (Tm, Val, Stage) =
    (arithOps.get(op), cmpOps.get(op)) match
      case (Some(aop), _) => inferArith(c, aop, l, r, st)
      case (_, Some(cop)) => inferComparison(c, cop, l, r)
      case _ => error("E0001", s"unknown operator `$op`", span)

  private def inferArith(c: Cxt, op: ArithOp, l: Tree, r: Tree, st: Option[Stage]): (Tm, Val, Stage) =
    val (first, second, swapped) = order(l, r)
    val (ft, fty, s) = st match
      case Some(s) =>
        val (t1, ty1) = inferS(c, first, s)
        (t1, ty1, s)
      case None => infer(c, first)
    if s == Stage.S1 then operandType(c, op, fty, first.span)
    val st2 = check(c, second, fty, s)
    val (a, b) = if swapped then (st2, ft) else (ft, st2)
    (Tm.Arith(op, a, b, s), fty, s)

  /** Comparisons are object formulas. */
  private def inferComparison(c: Cxt, op: CmpOp, l: Tree, r: Tree): (Tm, Val, Stage) = (l, r) match
    case (v: VarRef, agg: Agg) if op == CmpOp.Eq => inferAggregate(c, v, agg)
    case _ if isAggregate(l) || isAggregate(r) =>
      error("E0202", "an aggregate must be bound to a variable, `X = count { ... }`", l.span.to(r.span))
    case _ => inferPlainComparison(c, op, l, r)

  private def inferPlainComparison(c: Cxt, op: CmpOp, l: Tree, r: Tree): (Tm, Val, Stage) =
    val (first, second, swapped) = order(l, r)
    val (ft, fty) = inferS(c, first, Stage.S0)
    val st2 = check(c, second, fty, Stage.S0)
    val (a, b) = if swapped then (st2, ft) else (ft, st2)
    (Tm.Obj(ObjForm.Compare(op), List(a, b)), Val.PropT, Stage.S0)

  /** Arithmetic checked against a known type: both operands are checked against it. */
  def checkArith(c: Cxt, op: String, l: Tree, r: Tree, ty: Val, st: Stage, span: Span): Tm =
    val aop = arithOps(op)
    if st == Stage.S1 then operandType(c, aop, ty, span)
    Tm.Arith(aop, check(c, l, ty, st), check(c, r, ty, st), st)

  /** Negation, and the connectives of formulas. */
  def inferFormulaOrNegation(c: Cxt, t: Tree): (Tm, Val, Stage) =
    def formula(x: Tree) = check(c, x, Val.PropT, Stage.S0)
    t match
      case Neg(a) =>
        val (at, aty, s) = infer(c, a)
        if s == Stage.S1 then numeric(c, aty, a.span)
        (Tm.Negate(at, s), aty, s)
      case Not(a) => (Tm.Obj(ObjForm.Not, List(formula(a))), Val.PropT, Stage.S0)
      case Conj(a, b) => (Tm.Obj(ObjForm.And, List(formula(a), formula(b))), Val.PropT, Stage.S0)
      case Disj(a, b) => (Tm.Obj(ObjForm.Or, List(formula(a), formula(b))), Val.PropT, Stage.S0)
      case other => unsupported(other)

  private def numeric(c: Cxt, ty: Val, span: Span): Unit = force(ty) match
    case Val.Base(BaseType.IntT | BaseType.FloatT, _) | Val.Flex(_, _) =>
    case other => error("E0901", "mismatched types", span, s"expected a number, found `${show(c, other)}`")

  private def operandType(c: Cxt, op: ArithOp, ty: Val, span: Span): Unit = op match
    case ArithOp.Concat =>
      force(ty) match
        case Val.Base(BaseType.StringT, _) | Val.Flex(_, _) =>
        case other => error("E0901", "mismatched types", span, s"expected a string, found `${show(c, other)}`")
    case _ => numeric(c, ty, span)
