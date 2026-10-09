package hugin.core
package objtype

import hugin.obj.{ArithOp, BaseType, CmpOp, VarName}
import hugin.syntax.{AggKind, Literal}
import hugin.util.Span
import hugin.util.diagnostics.Problem
import scala.collection.mutable

/** Object typing of one scope (reference: object/types): the heads (constructing positions) and the body
 *  (matching positions) of a rule, a query or a piece of object code. A variable's type is the meet of
 *  the types of the positions it occupies in the body (E0401); variables without such positions are typed
 *  by equations and aggregates; then every position is checked (E0402–E0405, E0303–E0305). `run` returns
 *  the problems found and the variable types. `constructing` are further terms at constructing positions
 *  of known types (object code passed to a meta function in a head, a term of object code at its type). */
final class ObjCheck(
    types: ObjTypes,
    heads: List[OTerm],
    body: List[OFormula],
    constructing: List[(OTerm, OTy, String)] = Nil
):
  private val expected = mutable.LinkedHashMap.empty[String, mutable.ListBuffer[(OTy, Span, String)]]
  private val gamma = mutable.LinkedHashMap.empty[String, OTy]
  private val problems = mutable.ListBuffer.empty[Problem]
  import types.{isSub, baseOf, isRelLike, isClosed, meet}

  private def report(p: Problem): Unit = problems += p
  private def ty(t: OTy): TyName = TyName(types.show(t))
  private def const(r: RelInfo): ConstName = ConstName(r.name)
  private def known(t: OTy): Boolean = !t.vague

  /** Whether the checks of an operand of type `t` can be decided: not for an unknown type, nor for an
   *  abstract one (a functor's parameter type: they are decided for each instance). */
  private def decided(t: OTy): Boolean = known(t) && !types.isAbstract(t)

  private def expect(v: String, t: OTy, span: Span, where: String): Unit =
    expected.getOrElseUpdate(v, mutable.ListBuffer.empty) += ((t, span, where))

  private def column(r: RelInfo, i: Int): String =
    s"column ${i + 1}${r.cols(i)._1.map(l => s" (`$l`)").getOrElse("")} of `${r.name}`"

  private def expectArgs(r: RelInfo, args: List[OTerm]): Unit =
    for ((a, (_, colT)), i) <- args.zip(r.cols).zipWithIndex do expectPattern(a, colT, column(r, i))

  private def expectPattern(t: OTerm, colT: OTy, where: String): Unit = t match
    case OTerm.Var(n, sp) => expect(n, colT, sp, where)
    case OTerm.App(Some(r), args, _) => expectArgs(r, args)
    case OTerm.As(x, v, sp) =>
      val pt = x match
        case OTerm.App(Some(r), _, _) => r.fact
        case OTerm.Ascr(_, tp, _) => tp
        case _ => colT
      expect(v, pt, sp, s"`as` binding in $where")
      expectPattern(x, colT, where)
    case OTerm.Ascr(x, tp, _) =>
      expectPattern(x, colT, where)
      expectPattern(x, tp, s"ascription in $where")
    case _ =>

  private def collectExpected(f: OFormula): Unit = f match
    case OFormula.Atom(r, args, as, sp) =>
      expectArgs(r, args)
      as.foreach(v => expect(v, r.fact, sp, s"`as` binding of `${r.name}`"))
    case OFormula.Not(a, _) => collectExpected(a)
    case OFormula.Agg(_, _, _, b, _) => b.foreach(collectExpected)
    case OFormula.Disj(alts, _) => alts.flatten.foreach(collectExpected)
    case OFormula.Expect(t, tp, where, _) => expectPattern(t, tp, where)
    case _ =>

  /** The type of a term, if it can be determined. */
  def synth(t: OTerm): Option[OTy] = t match
    case OTerm.Var(n, _) => gamma.get(n)
    case OTerm.Lit(l, _) => Some(OTy.Base(BaseType.of(l)))
    case OTerm.Code(tp, _) => Option.when(tp != OTy.Unknown)(tp)
    case OTerm.App(Some(r), _, _) => Some(r.fact)
    case OTerm.App(None, _, _) => None
    case OTerm.As(x, _, _) => synth(x)
    case OTerm.Ascr(_, tp, _) => Some(tp)
    case OTerm.Arith(op, l, r, _) =>
      if op == ArithOp.Concat then Some(OTy.Str)
      else synth(l).flatMap(baseOf).orElse(synth(r).flatMap(baseOf)).map(OTy.Base(_))
    case OTerm.Neg(x, _) => synth(x).flatMap(baseOf).map(OTy.Base(_))
    case OTerm.Proj(OTerm.Var(x, _), l, _) =>
      gamma.get(x).filter(isClosed).flatMap(tx => types.commonLabel(tx, l).toOption.flatMap(cs => types.join(cs.map(_._3))))
    case OTerm.Proj(OTerm.Code(tx, _), l, _) if isClosed(tx) =>
      types.commonLabel(tx, l).toOption.flatMap(cs => types.join(cs.map(_._3)))
    case OTerm.With(OTerm.Var(x, _), _, _) => gamma.get(x)
    case OTerm.With(OTerm.Code(tx, _), _, _) => Option.when(known(tx))(tx)
    case _ => None

  def run(): (List[Problem], Map[String, OTy]) =
    body.foreach(collectExpected)
    for (v, occs) <- expected do
      var cur: Option[OTy] = Some(occs.head._1)
      var failedAt = -1
      for ((t, _, _), i) <- occs.zipWithIndex.drop(1) if cur.isDefined do
        val m = meet(cur.get, t)
        if m.isEmpty then failedAt = i
        cur = m
      cur match
        case Some(t) => gamma(v) = t
        case None =>
          val (failedType, failedSpan, _) = occs(failedAt)
          val others = occs.distinctBy(_._1).collect { case (t, sp, _) if sp != failedSpan => (ty(t), sp) }
          val expectations = occs.map((t, _, w) => (ty(t), w)).distinctBy((t, w) => (t.shown, w))
          report(ObjTypeError.NoMeet(VarName(v), (ty(failedType), failedSpan), others.toList, expectations.toList))
          gamma(v) = OTy.Err
    equations()
    for h <- heads do
      h match
        case OTerm.App(Some(r), args, _) => checkArgs(r, args, inHead = true)
        case OTerm.App(None, _, _) | OTerm.Code(_, _) =>
        case other => report(ObjTypeError.HeadNotAtom(other.span))
    for (t, tp, where) <- constructing do checkTerm(t, Some(tp), inHead = true, where)
    body.foreach(checkFormula)
    (problems.toList, gamma.toMap)

  /** Types the variables without positions in the body by equations and aggregates, to a fixed point. */
  private def equations(): Unit =
    var changed = true
    def bind(x: String, t: Option[OTy]): Unit =
      t.foreach { tx =>
        gamma(x) = tx
        changed = true
      }
    def eqs(fs: List[OFormula]): Unit = fs.foreach {
      case OFormula.Cmp(CmpOp.Eq, OTerm.Var(x, _), e, _) if !gamma.contains(x) => bind(x, synth(e))
      case OFormula.Cmp(CmpOp.Eq, e, OTerm.Var(x, _), _) if !gamma.contains(x) => bind(x, synth(e))
      case OFormula.Agg(res, k, t, b, _) =>
        eqs(b)
        if !gamma.contains(res) then bind(res, if k == AggKind.Count then Some(OTy.Int) else synth(t))
      case OFormula.Disj(alts, _) => alts.foreach(eqs)
      case OFormula.Atom(_, args, _, _) => args.foreach(asT)
      case _ =>
    }
    def asT(t: OTerm): Unit = t match
      case OTerm.As(x, v, _) =>
        if !gamma.contains(v) then bind(v, synth(x))
        asT(x)
      case OTerm.App(_, as, _) => as.foreach(asT)
      case _ =>
    while changed do
      changed = false
      eqs(body)

  private def litOk(l: Literal, col: OTy): Boolean =
    val bt = BaseType.of(l)
    !decided(col) || isSub(OTy.Base(bt), col) || baseOf(col).contains(bt)

  private def checkArgs(r: RelInfo, args: List[OTerm], inHead: Boolean): Unit =
    for ((a, (_, col)), i) <- args.zip(r.cols).zipWithIndex do checkTerm(a, Some(col), inHead, column(r, i))

  private def mismatch(t: OTerm, found: OTy, exp: OTy, where: String): Unit =
    report(ObjTypeError.Mismatch(ty(found), ty(exp), where, t.span))

  private def checkTerm(t: OTerm, col: Option[OTy], inHead: Boolean, where: String): Unit = t match
    case OTerm.Var(n, _) =>
      if inHead then
        (gamma.get(n), col) match
          case (Some(tv), Some(ct)) if !isSub(tv, ct) => mismatch(t, tv, ct, where)
          case _ =>
    case OTerm.Lit(l, _) =>
      col.foreach(ct => if !litOk(l, ct) then mismatch(t, OTy.Base(BaseType.of(l)), ct, where))
    case OTerm.Code(tp, _) =>
      // code whose shape is unknown: it must fit a constructing position, and meet a matching one
      col.foreach(ct => if known(tp) && (if inHead then !isSub(tp, ct) else meet(tp, ct).isEmpty) then mismatch(t, tp, ct, where))
    case OTerm.App(Some(r), args, _) =>
      col.foreach { ct =>
        if !isSub(r.fact, ct) then
          if inHead then mismatch(t, r.fact, ct, where)
          else report(ObjTypeError.PatternNeverMatches(const(r), ty(ct), where, t.span))
      }
      checkArgs(r, args, inHead)
    case OTerm.App(None, args, _) => args.foreach(checkTerm(_, None, inHead, where))
    case OTerm.As(x, _, _) => checkTerm(x, col, inHead, where)
    case OTerm.Ascr(x, tp, _) if !x.isInstanceOf[OTerm.Var] && synth(x).exists(sx => known(sx) && isSub(sx, tp)) =>
      // a term that is not a variable has its synthesized type and every supertype of it
      checkTerm(x, col, inHead, where)
    case OTerm.Ascr(x, tp, _) => checkAscription(t, x, tp, col, inHead, where)
    case OTerm.Arith(op, l, r, _) => checkArith(t, op, l, r, col, inHead, where)
    case OTerm.Neg(x, _) =>
      checkTerm(x, None, inHead, where)
      synth(x).foreach(tx =>
        if decided(tx) && !baseOf(tx).exists(_ != BaseType.StringT) then report(ObjTypeError.UnaryMinus(ty(tx), t.span))
      )
    case OTerm.Proj(OTerm.Var(x, _), l, _) => ObjRecords.checkProj(this, types, t, x, l, col, inHead, where)
    case OTerm.Proj(OTerm.Code(tx, _), l, _) =>
      // spliced code (a formula function's parameter): it stands for a variable or a fact once staged
      if isClosed(tx) then
        types.commonLabel(tx, l).left.foreach(missing => report(RecordError.NoCommonLabel(l, missing.map(const), None, t.span)))
    case OTerm.Proj(other, _, _) => report(RecordError.ProjectionOfNonVariable(other.span))
    case OTerm.With(OTerm.Var(x, _), fields, _) => ObjRecords.checkWith(this, types, t, x, fields, col, inHead, where)
    case OTerm.With(OTerm.Code(_, _), fields, _) => fields.foreach(f => checkTerm(f._2, None, inHead, where))
    case OTerm.With(other, _, _) => report(RecordError.UpdateOfNonVariable(other.span))

  /** An ascription `(x : tp)` whose term does not already have a subtype of `tp`: a checked downcast. */
  private def checkAscription(t: OTerm, x: OTerm, tp: OTy, col: Option[OTy], inHead: Boolean, where: String): Unit =
    val inner = col.orElse(synth(x)).getOrElse(OTy.Unknown)
    if synth(x).contains(OTy.Err) || !decided(inner) || !decided(tp) then ()
    else if !(isSub(tp, inner) && types.members(tp).toSet.subsetOf(types.members(inner).toSet)) then
      report(ObjTypeError.AscriptionNotSelecting(ty(tp), ty(inner), t.span))
    else if !isRelLike(tp) && tp != inner then report(ObjTypeError.AscriptionNotTestable(t.span))
    checkTerm(x, None, inHead, where)

  private def checkArith(t: OTerm, op: ArithOp, l: OTerm, r: OTerm, col: Option[OTy], inHead: Boolean, where: String): Unit =
    checkTerm(l, None, inHead, where)
    checkTerm(r, None, inHead, where)
    (synth(l), synth(r)) match
      case (Some(a), Some(b)) if decided(a) && decided(b) =>
        val (bl, br) = (baseOf(a), baseOf(b))
        val ok =
          bl.isDefined && bl == br && (if op == ArithOp.Concat then bl.contains(BaseType.StringT) else !bl.contains(BaseType.StringT))
        if !ok then report(ObjTypeError.ArithOperands(op, ty(a), ty(b), t.span))
        else
          col.foreach(ct => bl.foreach(b => if !isSub(OTy.Base(b), ct) && !baseOf(ct).contains(b) then mismatch(t, OTy.Base(b), ct, where)))
      case _ =>

  private[objtype] def problem(p: Problem): Unit = report(p)
  private[objtype] def typeOfVar(x: String): Option[OTy] = gamma.get(x)
  private[objtype] def term(t: OTerm, col: Option[OTy], inHead: Boolean, where: String): Unit = checkTerm(t, col, inHead, where)
  private[objtype] def mismatchAt(t: OTerm, found: OTy, exp: OTy, where: String): Unit = mismatch(t, found, exp, where)
  private[objtype] def tyName(t: OTy): TyName = ty(t)

  private def checkFormula(f: OFormula): Unit = f match
    case OFormula.Atom(r, args, _, _) => checkArgs(r, args, inHead = false)
    case OFormula.Expect(t, tp, where, _) => checkTerm(t, Some(tp), inHead = false, where)
    case OFormula.Not(a, _) => checkFormula(a)
    case OFormula.Cmp(op, l, r, sp) =>
      checkTerm(l, None, inHead = false, "comparison")
      checkTerm(r, None, inHead = false, "comparison")
      (synth(l), synth(r)) match
        case (Some(a), Some(b)) if decided(a) && decided(b) =>
          val ok = op match
            case CmpOp.Eq | CmpOp.Ne => (baseOf(a).isDefined && baseOf(a) == baseOf(b)) || (isRelLike(a) && isRelLike(b))
            case _ => baseOf(a).isDefined && baseOf(a) == baseOf(b)
          if !ok then report(ObjTypeError.Incomparable(op, ty(a), ty(b), sp))
        case _ =>
    case OFormula.Agg(_, k, t, b, _) =>
      b.foreach(checkFormula)
      checkTerm(t, None, inHead = false, "aggregate")
      if k != AggKind.Count then
        synth(t).foreach { tt =>
          val bt = baseOf(tt)
          val ok = if k == AggKind.Sum then bt.contains(BaseType.IntT) || bt.contains(BaseType.FloatT) else bt.isDefined
          if !ok && decided(tt) then report(ObjTypeError.AggregateOperand(k, ty(tt), t.span))
        }
    case OFormula.Disj(alts, _) => alts.flatten.foreach(checkFormula)
