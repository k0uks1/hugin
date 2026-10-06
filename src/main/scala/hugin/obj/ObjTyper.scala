package hugin.obj

import hugin.util.*
import hugin.core.*
import hugin.syntax.{AggKind, Literal}
import scala.collection.mutable

/** Mini phase: fold object-level arithmetic over literals (Proposition 3.1). Undefined folds are kept
 *  (the rule then never fires) and reported as a warning. */
final class ConstFold extends MiniPhase:
  def phaseName = "constFold"
  def description = "fold literal arithmetic"

  private def fold(t: Term, warn: Diagnostic => Unit): Term = t match
    case a @ Term.Arith(op, l, r) =>
      (fold(l, warn), fold(r, warn)) match
        case (Term.Lit(x), Term.Lit(y)) if BaseType.of(x) == BaseType.of(y) =>
          Prims.arith(op, x, y) match
            case Some(v) => Term.Lit(v)(a.span)
            case None =>
              warn(Diagnostic.warning("W0001", "undefined constant expression", a.span, s"`${x.show} ${op.show} ${y.show}` is undefined")
                .withNote("the formula containing it never holds, so this rule instance never fires"))
              Term.Arith(op, Term.Lit(x)(l.span), Term.Lit(y)(r.span))(a.span)
        case (fl, fr) => Term.Arith(op, fl, fr)(a.span)
    case n @ Term.Neg(x) =>
      fold(x, warn) match
        case Term.Lit(v) => Prims.neg(v).map(Term.Lit(_)(n.span)).getOrElse(Term.Neg(Term.Lit(v)(x.span))(n.span))
        case fx => Term.Neg(fx)(n.span)
    case a @ Term.App(r, args) => Term.App(r, args.map(fold(_, warn)))(a.span)
    case a @ Term.As(x, v) => Term.As(fold(x, warn), v)(a.span)
    case a @ Term.Ascr(x, tp) => Term.Ascr(fold(x, warn), tp)(a.span)
    case w @ Term.With(v, fs) => Term.With(v, fs.map((l, x, s) => (l, fold(x, warn), s)))(w.span)
    case other => other

  private def foldF(f: Formula, warn: Diagnostic => Unit): Formula = f match
    case a @ Formula.Atom(r, args, as) => Formula.Atom(r, args.map(fold(_, warn)), as)(a.span)
    case c @ Formula.Cmp(op, l, r) => Formula.Cmp(op, fold(l, warn), fold(r, warn))(c.span)
    case n @ Formula.Not(a) => Formula.Not(foldF(a, warn).asInstanceOf[Formula.Atom])(n.span)
    case g @ Formula.Agg(res, k, t, b) => Formula.Agg(res, k, fold(t, warn), b.map(foldF(_, warn)))(g.span)
    case d @ Formula.Disj(alts) => Formula.Disj(alts.map(_.map(foldF(_, warn))))(d.span)
    case other => other

  override def transformRule(r: Rule)(using Context): List[Rule] =
    val warn = (d: Diagnostic) => ctx.report(Diag.rule(r)(d))
    List(r.withParts(heads = r.heads.map(fold(_, warn)), body = r.body.map(foldF(_, warn))))
  override def transformQuery(q: Query)(using Context): Query =
    q.withBody(q.body.map(foldF(_, d => ctx.report(Diag.query(q)(d)))))

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
        case Some(g) => ctx.unit.varTypes.put(r, g); true
        case None => false
    }
    p.queries = p.queries.filter { q =>
      RuleTyper(ops, Nil, q.body, Diag.query(q)).run() match
        case Some(g) => ctx.unit.varTypes.put(q, g); true
        case None => false
    }

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
          if !ops.isBaseLike(b) && b != OType.Err then
            ctx.report(Diagnostic.error("E0404", s"`${t.name}` refines `${b.show}`, which is not a base type or refinement", t.span)
              .withOrigin(t.origin))
          else
            // cycle check
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
              ctx.report(Diagnostic.error("E0404", s"cyclic refinement `${t.name}`", t.span).withOrigin(t.origin))
        case _ =>
    for e <- p.edges do
      e.sub match
        case OType.Fact(_, _) | OType.Err => ()
        case OType.Con(s, _) if s.isOpen => ()
        case other =>
          ctx.report(Diagnostic.error(
            "E0404",
            s"`${other.show}` cannot be a member of the open type `${e.sup.name}`",
            e.span,
            "expected a fact type or an open type"
          ).withOrigin(e.origin))
    def checkType(t: OType, span: Span, origin: Origin): Unit = t match
      case OType.Union(ms) =>
        for m <- ms if !ops.isRelLike(m) do
          ctx.report(Diagnostic.error("E0404", s"union member `${m.show}` is not a type of facts", span)
            .withNote("every type in a union must be a subtype of `rel` (Section 5.4)").withOrigin(origin))
        for i <- ms.indices; j <- ms.indices if i < j do
          val common = ops.members(ms(i)).intersect(ops.members(ms(j)))
          if common.nonEmpty then
            ctx.report(Diagnostic.error(
              "E0404",
              s"union members `${ms(i).show}` and `${ms(j).show}` overlap",
              span,
              s"both contain `${common.head.name}`"
            ).withOrigin(origin))
      case _ =>
    for r <- p.rels; c <- r.cols do checkType(c.tpe, r.span, r.origin)

/** Types one rule or query. */
final class RuleTyper(ops: TypeOps, heads: List[Term], body: List[Formula], wrap: Diagnostic => Diagnostic)(using Context):
  private val expected = mutable.LinkedHashMap.empty[String, mutable.ListBuffer[(OType, Span, String)]]
  private val gamma = mutable.LinkedHashMap.empty[String, OType]
  private val errorsBefore = ctx.reporter.errorCount

  private def report(d: Diagnostic): Unit = ctx.report(wrap(d))

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
          val distinct = occs.distinctBy(_._1)
          var d = Diagnostic.error(
            "E0401",
            s"no value can occur in all these positions",
            occs(failedAt)._2,
            s"`${Var.display(v)}` has type `${occs(failedAt)._1.show}` here"
          )
          for (t, sp, where) <- distinct if sp != occs(failedAt)._2 do
            d = d.withLabel(sp, s"`${Var.display(v)}` has type `${t.show}` here")
          d = d.withNote(
            s"`${Var.display(v)}` is expected to have type ${occs.map((t, _, w) => s"`${t.show}` ($w)").distinct.mkString(", ")}"
          )
          report(d)
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
        case other => report(Diagnostic.error("E0402", "the head of a rule must be a relation atom", other.span))
    body.foreach(checkFormula)
    if ctx.reporter.errorCount > errorsBefore then None else Some(gamma.toMap)

  private def litOk(l: Literal, col: OType): Boolean =
    val bt = BaseType.of(l)
    col == OType.Err || ops.isSub(OType.Base(bt), col) || ops.baseOf(col).contains(bt)

  private def checkArgs(c: RelSym, args: List[Term], inHead: Boolean): Unit =
    for ((a, col), i) <- args.zip(c.cols).zipWithIndex do checkTerm(a, Some(col.tpe), inHead, s"column ${i + 1} of `${c.name}`")

  private def mismatch(t: Term, found: OType, expected: OType, where: String): Unit =
    report(Diagnostic.error("E0402", "type mismatch", t.span, s"expected `${expected.show}`, found `${found.show}`")
      .withNote(s"in $where"))

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
            report(Diagnostic.error("E0402", s"pattern can never match", t.span, s"`${c.name}` facts are not of type `${ct.show}`")
              .withNote(s"in $where"))
      }
      checkArgs(c, args, inHead)
    case Term.As(x, _) => checkTerm(x, col, inHead, where)
    case Term.Ascr(x, tp) =>
      // τ is the type of the position (column) the ascribed term occupies, or its synthesized type
      val inner = col.orElse(synth(x)).getOrElse(OType.Err)
      if synth(x).contains(OType.Err) then () // already reported (no meet)
      else if !(ops.isSub(tp, inner) && ops.members(tp).subsetOf(ops.members(inner))) && inner != OType.Err then
        report(Diagnostic.error("E0405", "invalid ascription", t.span, s"`${tp.show}` does not select members of `${inner.show}`")
          .withNote("an ascription (t : T) is a checked downcast; T must be a subtype of the type of t"))
      else if !ops.isRelLike(tp) && tp != inner then
        report(Diagnostic.error("E0405", "invalid ascription", t.span, "only types of facts can be tested at run time"))
      checkTerm(x, None, inHead, where)
    case Term.Arith(op, l, r) =>
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
            report(Diagnostic.error("E0402", s"operator `${op.show}` cannot be applied to `${a.show}` and `${b.show}`", t.span)
              .withNote("`+ - * /` apply to two ints or two floats, `^` to two strings; ints and floats are never converted"))
          else
            col.foreach(ct =>
              bl.foreach(b => if !ops.isSub(OType.Base(b), ct) && !ops.baseOf(ct).contains(b) then mismatch(t, OType.Base(b), ct, where))
            )
        case _ =>
    case Term.Neg(x) =>
      checkTerm(x, None, inHead, where)
      synth(x).foreach(tx =>
        if !ops.baseOf(tx).exists(b => b != BaseType.StringT) && tx != OType.Err then
          report(Diagnostic.error("E0402", s"unary minus cannot be applied to `${tx.show}`", t.span))
      )
    case Term.Proj(v @ Term.Var(x), l) =>
      gamma.get(x) match
        case None =>
        case Some(OType.Err) =>
        case Some(tx) =>
          if !ops.isClosed(tx) then
            report(Diagnostic.error(
              "E0303",
              s"projection on a type that is not closed",
              t.span,
              s"`${Var.display(x)}` has type `${tx.show}`"
            )
              .withNote("projection and update require a fact type or a union of fact types; open types may gain constructors"))
          else
            ops.commonLabel(tx, l) match
              case Left(missing) =>
                report(Diagnostic.error(
                  "E0304",
                  s"no common label `$l`",
                  t.span,
                  s"not a column of ${missing.map(m => s"`${m.name}`").mkString(", ")}"
                )
                  .withNote(s"`${Var.display(x)}` has type `${tx.show}`; every member must have the label"))
              case Right(cs) =>
                ops.join(cs.map(_._3)) match
                  case None =>
                    report(Diagnostic.error(
                      "E0305",
                      s"undefined join for label `$l`",
                      t.span,
                      cs.map((c, _, ct) => s"`${ct.show}` in `${c.name}`").mkString(", ")
                    )
                      .withNote("the join of different base types is undefined"))
                  case Some(j) =>
                    col.foreach(ct => if inHead && !ops.isSub(j, ct) then mismatch(t, j, ct, where))
    case Term.Proj(other, _) =>
      report(Diagnostic.error("E0303", "projection applies only to variables", other.span, "bind this term to a variable first"))
    case Term.With(v @ Term.Var(x), fields) =>
      gamma.get(x) match
        case None | Some(OType.Err) =>
        case Some(tx) =>
          if !ops.isClosed(tx) then
            report(Diagnostic.error("E0303", s"update on a type that is not closed", t.span, s"`${Var.display(x)}` has type `${tx.show}`"))
          else
            for (l, h, sp) <- fields do
              ops.commonLabel(tx, l) match
                case Left(missing) =>
                  report(Diagnostic.error(
                    "E0304",
                    s"no common label `$l`",
                    sp,
                    s"not a column of ${missing.map(m => s"`${m.name}`").mkString(", ")}"
                  ))
                case Right(cs) =>
                  for (c, _, ct) <- cs do checkTerm(h, Some(ct), inHead = true, s"update of `$l` in `${c.name}`")
          col.foreach(ct => if inHead && !ops.isSub(tx, ct) then mismatch(t, tx, ct, where))
    case Term.With(other, _) =>
      report(Diagnostic.error("E0303", "update applies only to variables", other.span))
    case _ =>

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
            report(Diagnostic.error("E0402", s"cannot compare `${a.show}` with `${b.show}`", f.span, s"`${op.show}` on incompatible types")
              .withNote(if op == CmpOp.Eq || op == CmpOp.Ne then "both sides must have the same base type, or both be facts"
              else "ordering comparisons apply to two values of the same base type"))
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
            report(Diagnostic.error("E0402", s"`${k.show}` cannot aggregate values of type `${tt.show}`", t.span)
              .withNote(if k == AggKind.Sum then "sum applies to int or float" else s"${k.show} applies to base types"))
        }
    case Formula.Disj(alts) => alts.flatten.foreach(checkFormula)
    case _ =>
