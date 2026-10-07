package hugin.obj
package typing

import hugin.util.*
import hugin.util.diagnostics.Problem
import hugin.compiler.*
import hugin.syntax.{AggKind, Literal}
import scala.collection.mutable

/** Object-level type inference (Section 6.1, 6.2) and well-formedness of declarations (Section 5.4).
 *  Ill-typed rules are reported and removed so later phases see a well-typed program. */
final class ObjTyperPhase extends Phase:
  def phaseName = "objTyper"
  def description = "object-level type inference by meets; declaration well-formedness"

  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val ops = TypeOps(p)
    checkDecls(p, ops)
    p.rules = p.rules.filter { r =>
      RuleTyper(ops, r.heads, r.body, Diag.rule(r)).run() match
        case Some(g) =>
          ctx.unit.varTypes.put(r, g)
          recordVariables(r.span, r.heads, r.body, g)
          true
        case None => false
    }
    p.queries = p.queries.filter { q =>
      RuleTyper(ops, Nil, q.body, Diag.query(q)).run() match
        case Some(g) =>
          ctx.unit.varTypes.put(q, g)
          recordVariables(q.span, Nil, q.body, g)
          true
        case None => false
    }

  /** Records the inferred type of every object variable occurrence in the semantic index. */
  private def recordVariables(item: Span, heads: List[Term], body: List[Formula], g: Map[String, OType])(using Context): Unit =
    def note(span: Span, n: String) = g.get(n).foreach(tp => ctx.unit.index.variable(span, n, Var.display(n), tp.show, item))
    def term(t: Term): Unit = t match
      case v @ Term.Var(n) if !Var.isWild(n) => note(v.span, n)
      case Term.App(_, as) => as.foreach(term)
      case a @ Term.As(x, v) => term(x); note(a.span, v)
      case Term.Ascr(x, _) => term(x)
      case Term.Proj(v, _) => term(v)
      case Term.With(v, fs) => term(v); fs.foreach(f => term(f._2))
      case Term.Arith(_, l, r) => term(l); term(r)
      case Term.Neg(x) => term(x)
      case _ =>
    def formula(f: Formula): Unit = f match
      case Formula.Atom(_, as, _) => as.foreach(term)
      case Formula.Cmp(_, l, r) => term(l); term(r)
      case Formula.Not(a) => formula(a)
      case Formula.Agg(_, _, t, b) => term(t); b.foreach(formula)
      case Formula.Disj(alts) => alts.flatten.foreach(formula)
      case _ =>
    heads.foreach(term)
    body.foreach(formula)

  override def show(using Context): String =
    val p = ctx.unit.prog.nn
    val sb = StringBuilder(ObjPrinter.program(p))
    sb ++= "(* typing contexts *)\n"
    for r <- p.rules do
      val g = ctx.unit.varTypes.get(r)
      if g != null && g.nonEmpty then
        sb ++= s"(* ${r.name.map("@" + _).getOrElse(ObjPrinter.rule(r).take(40))}: ${g.toList.sortBy(_._1).map((v, t) => s"${Var.display(v)} : ${t.show}").mkString(", ")} *)\n"
    sb.toString

  private def checkDecls(p: ObjProgram, ops: TypeOps)(using Context): Unit =
    for t <- p.types do
      t.kind match
        case TypeKind.Refinement(b) =>
          // a cycle first: following it would not reach a base type
          val seen = mutable.HashSet(t)
          var cur = b
          var cyc = false
          while !cyc && (cur match { case OType.Con(s, _) => true; case _ => false }) do
            val OType.Con(s, _) = cur: @unchecked
            if !seen.add(s) then cyc = true
            else
              cur = s.kind match
                case TypeKind.Refinement(x) => x
                case _ => OType.Err
          if cyc then
            ctx.report(ObjTypeError.CyclicRefinement(t))
          else if !ops.isBaseLike(b) && b != OType.Err then
            ctx.report(ObjTypeError.RefinesNonBase(t, b))
        case _ =>
    for e <- p.edges do
      e.sub match
        case OType.Fact(_, _) | OType.Err => ()
        case OType.Con(s, _) if s.isOpen => ()
        case other =>
          ctx.report(ObjTypeError.NotOpenMember(other, e.sup, e.span, e.origin))
    def checkType(t: OType, span: Span, origin: Origin): Unit = t match
      case OType.Union(ms) =>
        for m <- ms if !ops.isRelLike(m) do
          ctx.report(ObjTypeError.UnionMemberNotFacts(m, span, origin))
        for i <- ms.indices; j <- ms.indices if i < j do
          val common = ops.members(ms(i)).intersect(ops.members(ms(j)))
          if common.nonEmpty then
            ctx.report(ObjTypeError.UnionOverlap(ms(i), ms(j), common.head, span, origin))
      case _ =>
    for r <- p.rels; c <- r.cols do checkType(c.tpe, r.span, r.origin)

/** Types one rule or query. */
final class RuleTyper(ops: TypeOps, heads: List[Term], body: List[Formula], wrap: Diagnostic => Diagnostic)(using Context):
  private val expected = mutable.LinkedHashMap.empty[String, mutable.ListBuffer[(OType, Span, String)]]
  private val gamma = mutable.LinkedHashMap.empty[String, OType]
  private val errorsBefore = ctx.reporter.errorCount

  private def report(p: Problem): Unit = ctx.report(wrap(p.toDiagnostic))

  private def expect(v: String, t: OType, span: Span, where: String): Unit =
    expected.getOrElseUpdate(v, mutable.ListBuffer.empty) += ((t, span, where))

  private def expectArgs(c: RelSym, args: List[Term]): Unit =
    for ((a, col), i) <- args.zip(c.cols).zipWithIndex do
      expectPattern(a, col.tpe, s"column ${i + 1}${col.label.map(l => s" (`$l`)").getOrElse("")} of `${c.name}`")

  private def expectPattern(t: Term, colT: OType, where: String): Unit = t match
    case v @ Term.Var(n) => expect(n, colT, v.span, where)
    case Term.App(RelRef.Sym(c), args) => expectArgs(c, args)
    case a @ Term.As(x, v) =>
      val pt = x match
        case Term.App(RelRef.Sym(c), _) => OType.Fact(c, Nil)
        case Term.Ascr(_, tp) => tp
        case _ => colT
      expect(v, pt, a.span, s"`as` binding in $where")
      expectPattern(x, colT, where)
    case a @ Term.Ascr(x, tp) =>
      expectPattern(x, colT, where)
      expectPattern(x, tp, s"ascription in $where")
    case _ =>

  private def collectExpected(f: Formula): Unit = f match
    case a @ Formula.Atom(RelRef.Sym(c), args, as) =>
      expectArgs(c, args)
      as.foreach(v => expect(v, OType.Fact(c, Nil), a.span, s"`as` binding of `${c.name}`"))
    case Formula.Not(a) => collectExpected(a)
    case Formula.Agg(_, _, _, b) => b.foreach(collectExpected)
    case Formula.Disj(alts) => alts.flatten.foreach(collectExpected)
    case _ =>

  private def synth(t: Term): Option[OType] = t match
    case Term.Var(n) => gamma.get(n)
    case Term.Lit(l) => Some(OType.Base(BaseType.of(l)))
    case Term.App(RelRef.Sym(c), _) => Some(OType.Fact(c, Nil))
    case Term.As(x, _) => synth(x)
    case Term.Ascr(_, tp) => Some(tp)
    case Term.Arith(op, l, r) =>
      if op == ArithOp.Concat then Some(OType.Str)
      else synth(l).flatMap(ops.baseOf).orElse(synth(r).flatMap(ops.baseOf)).map(OType.Base(_))
    case Term.Neg(x) => synth(x).flatMap(ops.baseOf).map(OType.Base(_))
    case Term.Proj(Term.Var(x), l) =>
      gamma.get(x).filter(ops.isClosed).flatMap { tx =>
        ops.commonLabel(tx, l) match
          case Right(cs) => ops.join(cs.map(_._3))
          case Left(_) => None
      }
    case Term.With(Term.Var(x), _) => gamma.get(x)
    case _ => None

  def run(): Option[Map[String, OType]] =
    body.foreach(collectExpected)
    // meets (Definition 6.1)
    for (v, occs) <- expected do
      var cur: Option[OType] = Some(occs.head._1)
      var failedAt = -1
      for ((t, _, _), i) <- occs.zipWithIndex.drop(1) if cur.isDefined do
        val m = ops.meet(cur.get, t)
        if m.isEmpty then failedAt = i
        cur = m
      cur match
        case Some(t) => gamma(v) = t
        case None =>
          val (failedType, failedSpan, _) = occs(failedAt)
          val others = occs.distinctBy(_._1).collect { case (t, sp, _) if sp != failedSpan => (t, sp) }
          val expectations = occs.map((t, _, w) => (t, w)).distinctBy((t, w) => (t.show, w))
          report(ObjTypeError.NoMeet(VarName(v), (failedType, failedSpan), others.toList, expectations.toList))
          gamma(v) = OType.Err
    // equations and aggregates
    var changed = true
    while changed do
      changed = false
      def eqs(fs: List[Formula]): Unit = fs.foreach {
        case Formula.Cmp(CmpOp.Eq, Term.Var(x), e) if !gamma.contains(x) =>
          synth(e).foreach { t =>
            gamma(x) = t; changed = true
          }
        case Formula.Cmp(CmpOp.Eq, e, Term.Var(x)) if !gamma.contains(x) =>
          synth(e).foreach { t =>
            gamma(x) = t; changed = true
          }
        case Formula.Agg(res, k, t, b) =>
          eqs(b)
          if !gamma.contains(res) then
            val rt = if k == AggKind.Count then Some(OType.Int) else synth(t)
            rt.foreach { x =>
              gamma(res) = x; changed = true
            }
        case Formula.Disj(alts) => alts.foreach(eqs)
        case Formula.Atom(_, args, _) =>
          // `as` on nested terms
          def asT(t: Term): Unit = t match
            case Term.As(x, v) if !gamma.contains(v) =>
              synth(x).foreach { tx =>
                gamma(v) = tx; changed = true
              }; asT(x)
            case Term.App(_, as) => as.foreach(asT)
            case Term.As(x, _) => asT(x)
            case _ =>
          args.foreach(asT)
        case _ =>
      }
      eqs(body)
    // checks by subsumption
    for h <- heads do
      h match
        case Term.App(RelRef.Sym(c), args) => checkArgs(c, args, inHead = true)
        case other => report(ObjTypeError.HeadNotAtom(other.span))
    body.foreach(checkFormula)
    if ctx.reporter.errorCount > errorsBefore then None else Some(gamma.toMap)

  private def litOk(l: Literal, col: OType): Boolean =
    val bt = BaseType.of(l)
    col == OType.Err || ops.isSub(OType.Base(bt), col) || ops.baseOf(col).contains(bt)

  private def checkArgs(c: RelSym, args: List[Term], inHead: Boolean): Unit =
    for ((a, col), i) <- args.zip(c.cols).zipWithIndex do checkTerm(a, Some(col.tpe), inHead, s"column ${i + 1} of `${c.name}`")

  private def mismatch(t: Term, found: OType, expected: OType, where: String): Unit =
    report(ObjTypeError.Mismatch(found, expected, where, t.span))

  private def checkTerm(t: Term, col: Option[OType], inHead: Boolean, where: String): Unit = t match
    case Term.Var(n) =>
      if inHead then
        (gamma.get(n), col) match
          case (Some(tv), Some(ct)) if !ops.isSub(tv, ct) => mismatch(t, tv, ct, where)
          case _ =>
    case Term.Lit(l) =>
      col.foreach(ct => if !litOk(l, ct) then mismatch(t, OType.Base(BaseType.of(l)), ct, where))
    case Term.App(RelRef.Sym(c), args) =>
      col.foreach { ct =>
        if !ops.isSub(OType.Fact(c, Nil), ct) then
          if inHead then mismatch(t, OType.Fact(c, Nil), ct, where)
          else
            report(ObjTypeError.PatternNeverMatches(c, ct, where, t.span))
      }
      checkArgs(c, args, inHead)
    case Term.As(x, _) => checkTerm(x, col, inHead, where)
    case Term.Ascr(x, tp) if !x.isInstanceOf[Term.Var] && synth(x).exists(sx => sx != OType.Err && ops.isSub(sx, tp)) =>
      // a term that is not a variable has its synthesized type, and by subsumption every supertype of it:
      // `(nil : list int)` ascribes the constructor term with its declared result type (`Γ ⊢ t : τ` with
      // τ = T), which always holds; the term must still fit the position
      checkTerm(x, col, inHead, where)
    case Term.Ascr(x, tp) => checkAscription(t, x, tp, col, inHead, where)
    case Term.Arith(op, l, r) => checkArith(t, op, l, r, col, inHead, where)
    case Term.Neg(x) =>
      checkTerm(x, None, inHead, where)
      synth(x).foreach(tx =>
        if !ops.baseOf(tx).exists(b => b != BaseType.StringT) && tx != OType.Err then
          report(ObjTypeError.UnaryMinus(tx, t.span))
      )
    case Term.Proj(Term.Var(x), l) => checkProj(t, x, l, col, inHead, where)
    case Term.Proj(other, _) =>
      report(RecordError.ProjectionOfNonVariable(other.span))
    case Term.With(Term.Var(x), fields) => checkWith(t, x, fields, col, inHead, where)
    case Term.With(other, _) =>
      report(RecordError.UpdateOfNonVariable(other.span))
    case _ =>

  /** An ascription `(x : tp)` whose term does not already have a subtype of `tp`: a checked downcast. */
  private def checkAscription(t: Term, x: Term, tp: OType, col: Option[OType], inHead: Boolean, where: String): Unit =
    // τ is the type of the position (column) the ascribed term occupies, or its synthesized type
    val inner = col.orElse(synth(x)).getOrElse(OType.Err)
    if synth(x).contains(OType.Err) then () // already reported (no meet)
    else if !(ops.isSub(tp, inner) && ops.members(tp).subsetOf(ops.members(inner))) && inner != OType.Err then
      report(ObjTypeError.AscriptionNotSelecting(tp, inner, t.span))
    else if !ops.isRelLike(tp) && tp != inner then
      report(ObjTypeError.AscriptionNotTestable(t.span))
    checkTerm(x, None, inHead, where)

  private def checkArith(t: Term, op: ArithOp, l: Term, r: Term, col: Option[OType], inHead: Boolean, where: String): Unit =
    checkTerm(l, None, inHead, where)
    checkTerm(r, None, inHead, where)
    val (tl, tr) = (synth(l), synth(r))
    val bl = tl.flatMap(ops.baseOf)
    val br = tr.flatMap(ops.baseOf)
    (tl, tr) match
      case (Some(a), Some(b)) =>
        val ok = bl.isDefined && bl == br && (op match
          case ArithOp.Concat => bl.contains(BaseType.StringT)
          case _ => !bl.contains(BaseType.StringT)
        )
        if !ok && a != OType.Err && b != OType.Err then
          report(ObjTypeError.ArithOperands(op, a, b, t.span))
        else
          col.foreach(ct =>
            bl.foreach(b => if !ops.isSub(OType.Base(b), ct) && !ops.baseOf(ct).contains(b) then mismatch(t, OType.Base(b), ct, where))
          )
      case _ =>

  /** A projection `X.l` (Section 6.2): X has a closed type whose members all have the label `l`. */
  private def checkProj(t: Term, x: String, l: String, col: Option[OType], inHead: Boolean, where: String): Unit =
    gamma.get(x) match
      case None =>
      case Some(OType.Err) =>
      case Some(tx) =>
        if !ops.isClosed(tx) then
          report(RecordError.ProjectionNotClosed(VarName(x), tx, t.span))
        else
          ops.commonLabel(tx, l) match
            case Left(missing) =>
              report(RecordError.NoCommonLabel(l, missing, Some((VarName(x), tx)), t.span))
            case Right(cs) =>
              ops.join(cs.map(_._3)) match
                case None =>
                  report(RecordError.UndefinedJoin(l, cs.map((c, _, ct) => (c, ct)), t.span))
                case Some(j) =>
                  col.foreach(ct => if inHead && !ops.isSub(j, ct) then mismatch(t, j, ct, where))

  /** An update `(X with { l = h, ... })` (Section 6.2). */
  private def checkWith(t: Term, x: String, fields: List[(String, Term, Span)], col: Option[OType], inHead: Boolean, where: String): Unit =
    gamma.get(x) match
      case None | Some(OType.Err) =>
      case Some(tx) =>
        if !ops.isClosed(tx) then
          report(RecordError.UpdateNotClosed(VarName(x), tx, t.span))
        else
          for (l, h, sp) <- fields do
            ops.commonLabel(tx, l) match
              case Left(missing) =>
                report(RecordError.NoCommonLabel(l, missing, None, sp))
              case Right(cs) =>
                for (c, _, ct) <- cs do checkTerm(h, Some(ct), inHead = true, s"update of `$l` in `${c.name}`")
        col.foreach(ct => if inHead && !ops.isSub(tx, ct) then mismatch(t, tx, ct, where))

  private def checkFormula(f: Formula): Unit = f match
    case Formula.Atom(RelRef.Sym(c), args, _) => checkArgs(c, args, inHead = false)
    case Formula.Not(a) => checkFormula(a)
    case Formula.Cmp(op, l, r) =>
      checkTerm(l, None, inHead = false, "comparison")
      checkTerm(r, None, inHead = false, "comparison")
      (synth(l), synth(r)) match
        case (Some(a), Some(b)) if a != OType.Err && b != OType.Err =>
          val ok = op match
            case CmpOp.Eq | CmpOp.Ne =>
              (ops.baseOf(a).isDefined && ops.baseOf(a) == ops.baseOf(b)) || (ops.isRelLike(a) && ops.isRelLike(b))
            case _ => ops.baseOf(a).isDefined && ops.baseOf(a) == ops.baseOf(b)
          if !ok then
            report(ObjTypeError.Incomparable(op, a, b, f.span))
        case _ =>
    case Formula.Agg(res, k, t, b) =>
      b.foreach(checkFormula)
      checkTerm(t, None, inHead = false, "aggregate")
      if k != AggKind.Count then
        synth(t).foreach { tt =>
          val bt = ops.baseOf(tt)
          val ok = k match
            case AggKind.Sum => bt.contains(BaseType.IntT) || bt.contains(BaseType.FloatT)
            case _ => bt.isDefined
          if !ok && tt != OType.Err then
            report(ObjTypeError.AggregateOperand(k, tt, t.span))
        }
    case Formula.Disj(alts) => alts.flatten.foreach(checkFormula)
    case _ =>
