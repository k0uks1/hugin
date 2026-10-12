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

  def isIntLit(t: Tree): Boolean = t match
    case Lit(hugin.syntax.Literal.IntL(_)) => true
    case Parens(i) => isIntLit(i)
    case Neg(i) => isIntLit(i)
    case _ => false

  /** The operand to infer first (not a literal, if possible) and the other one; `true` if swapped. */
  def order(l: Tree, r: Tree): (Tree, Tree, Boolean) =
    if isLit(l) && !isLit(r) then (r, l, true) else (l, r, false)

  /** `l op r` inferred, at stage `st` if known. `first` is the operand inferred first ([[order]]) if it was
   *  already, to choose between the bindings of the operator ([[Overloading]]). */
  def inferInfix(
      c: Cxt,
      op: String,
      l: Tree,
      r: Tree,
      span: Span,
      st: Option[Stage],
      first: Option[(Tm, Val, Stage)] = None
  ): (Tm, Val, Stage) =
    (arithOps.get(op), cmpOps.get(op)) match
      case (Some(aop), _) => inferArith(c, aop, l, r, st, first)
      case (_, Some(cop)) => inferComparison(c, cop, l, r)
      // `≡` outside the meta level, where no binding applies
      case _ if op == "≡" => fail(OperatorProblem.NoneFits(op, Nil, None, None, span))
      case _ => fail(TypeProblem.UnknownOperator(op, span))

  private def inferArith(c: Cxt, op: ArithOp, l: Tree, r: Tree, st: Option[Stage], inferred: Option[(Tm, Val, Stage)]): (Tm, Val, Stage) =
    if st.contains(Stage.S0) then
      val (tm, ty) = objectArith(c, op, l, r)
      (tm, ty, Stage.S0)
    else
      val (first, second, swapped) = order(l, r)
      val (ft, fty, s) = (inferred, st) match
        case (Some(done), _) => done
        case (None, Some(s)) =>
          val (t1, ty1) = inferS(c, first, s)
          (t1, ty1, s)
        case (None, None) => infer(c, first)
      (natType(fty), successorCount(second)) match
        case (Some((_, suc)), Some(k)) if s == Stage.S1 && op == ArithOp.Add && !swapped =>
          // `e + k` on a nat-like type: the successor applied `k` times (reference: meta/families)
          (natSuccessor(suc, ft, k, first.span.to(second.span)), fty, s)
        case _ =>
          if s == Stage.S1 then operandType(c, op, fty, first.span)
          // an integer literal next to an operand of unknown type makes it an `int` at once: arithmetic
          // other than `e + k` is on base types (reference: meta/functions)
          if s == Stage.S1 && isIntLit(second) && force(fty).isInstanceOf[Val.Flex] then
            unifyAt(c, second.span, metaIntType, fty)
          val st2 = check(c, second, fty, s)
          val (a, b) = if swapped then (st2, ft) else (ft, st2)
          (if s == Stage.S1 then metaArith(op, a, b, fty) else Tm.Arith(op, a, b, s), fty, s)

  /** Comparisons are object formulas. */
  private def inferComparison(c: Cxt, op: CmpOp, l: Tree, r: Tree): (Tm, Val, Stage) = (l, r) match
    case (v: VarRef, agg: Agg) if op == CmpOp.Eq => inferAggregate(c, v, agg)
    case _ if isAggregate(l) || isAggregate(r) =>
      fail(ElabProblem.UnboundAggregate(l.span.to(r.span)))
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
    if st == Stage.S0 then objectArith(c, aop, l, r)._1
    else
      operandType(c, aop, ty, span)
      metaArith(aop, check(c, l, ty, st), check(c, r, ty, st), ty)

  /** Arithmetic at the meta level on operands of type `ty`: on the meta `int`, the function of `std/int`
   *  (reference: std/int), whose clauses define it; on the other meta primitives (and on operands whose
   *  type is still unknown) the primitive operation. */
  private def metaArith(op: ArithOp, a: Tm, b: Tm, ty: Val): Tm =
    intFunction(op.toString.toLowerCase, ty) match
      case Some(f) => Tm.App(Tm.App(Tm.Global(f), a, Icit.Expl), b, Icit.Expl)
      case None => Tm.Arith(op, a, b, Stage.S1)

  /** The function of `std/int` for the operation `key` (`add`, …, `neg`), if `ty` is the meta `int`. */
  private def intFunction(key: String, ty: Val): Option[Int] =
    if metaInt != null && isMetaInt(force(ty)) then intOperator(key) else None

  /** Arithmetic in object code. If both operands are compile-time primitives (and not both literals),
   *  it is computed at compile time and the result persisted as a literal (`q (k + 1)` with `k = 42`
   *  stages to `q 43`); otherwise it is object arithmetic, whose operand types object typing checks. On
   *  meta integers the object operation is computed exactly, so only the result must fit into 64 bits
   *  (E0930); a division by zero is undefined, as at the object level (E0909). */
  private def objectArith(c: Cxt, op: ArithOp, l: Tree, r: Tree): (Tm, Val) =
    val (lt, lty, ls) = insert(c, l.span, infer(c, l))
    val (rt, rty, rs) = insert(c, r.span, infer(c, r))
    (ls, rs, isMetaPrim(lty)) match
      case (Stage.S1, Stage.S1, Some(b)) if isMetaPrim(rty).isDefined && !(isLit(l) && isLit(r)) =>
        operandType(c, op, lty, l.span)
        unifyAt(c, r.span, lty, rty)
        (Tm.Persist(Tm.Arith(op, lt, rt, Stage.S1)), Val.Base(b, Stage.S0))
      case _ =>
        val (a, aty) = adjust(c, l.span, lt, lty, ls, Stage.S0)
        val (b, bty) = adjust(c, r.span, rt, rty, rs, Stage.S0)
        (Tm.Arith(op, located(l.span, a, aty, Stage.S0), located(r.span, b, bty, Stage.S0), Stage.S0), if ls == Stage.S0 then aty else bty)

  /** Negation, and the connectives of formulas. */
  def inferFormulaOrNegation(c: Cxt, t: Tree): (Tm, Val, Stage) =
    def formula(x: Tree) = check(c, x, Val.PropT, Stage.S0)
    t match
      case Neg(a) =>
        val (at, aty, s) = infer(c, a)
        if s == Stage.S1 then numeric(c, aty, a.span)
        val neg = if s == Stage.S1 then intFunction("neg", aty) else None
        (neg.fold(Tm.Negate(at, s))(f => Tm.App(Tm.Global(f), at, Icit.Expl)), aty, s)
      case Not(a) =>
        val f = formula(a)
        atomsOf(f).foreach((atom, span) => requireComplete(c, atom, span, "negates"))
        (Tm.Obj(ObjForm.Not, List(f)), Val.PropT, Stage.S0)
      case Conj(a, b) => (Tm.Obj(ObjForm.And, List(formula(a), formula(b))), Val.PropT, Stage.S0)
      case Disj(a, b) => (Tm.Obj(ObjForm.Or, List(formula(a), formula(b))), Val.PropT, Stage.S0)
      case other => unsupported(other)

  private def numeric(c: Cxt, ty: Val, span: Span): Unit = force(ty) match
    case Val.Base(BaseType.IntT | BaseType.FloatT, _) | Val.Flex(_, _) =>
    case t if isMetaInt(t) =>
    case other => fail(TypeProblem.NotNumeric(show(c, other), span))

  private def operandType(c: Cxt, op: ArithOp, ty: Val, span: Span): Unit = op match
    case ArithOp.Concat =>
      force(ty) match
        case Val.Base(BaseType.StringT, _) | Val.Flex(_, _) =>
        case other => fail(TypeProblem.NotString(show(c, other), span))
    case _ => numeric(c, ty, span)
