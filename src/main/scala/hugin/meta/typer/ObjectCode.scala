package hugin.meta
package typer

import hugin.util.*
import hugin.syntax.*
import hugin.syntax.Trees.*
import hugin.compiler.*
import hugin.obj.{Column, BaseType, ArithOp, CmpOp, RelRef, Expansion}
import hugin.obj
import scala.collection.mutable
import scala.util.chaining.*

/** Stage inference for object code: terms, formulas, heads and named patterns (Sections 2.4, 3.2). */
private[meta] trait ObjectCode extends TyperBase:
  self: Typer =>
  import MExpr.*
  import MType.*

  // ======================================================================= object code

  private[meta] def isPrimMeta(m: MExpr): Option[BaseType] = m match
    case Ref(s) => syms.mtype(s).collect { case Prim(b) => b }
    case MExpr.Lit(l) => Some(BaseType.of(l))
    case Op(_, l, _, _) => isPrimMeta(l)
    case MExpr.Neg(x, _) => isPrimMeta(x)
    case _ => None

  private[meta] def stage1(t: obj.Term): Option[MExpr] = t match
    case obj.Term.Splice(m) if isPrimMeta(m).isDefined => Some(m)
    case obj.Term.Lit(l) => Some(MExpr.Lit(l))
    case _ => None

  def elabTerm(t: Tree, sc: Scope, rc: RuleCtx): obj.Term = t match
    case Parens(i) => elabTerm(i, sc, rc)
    case Wildcard() => obj.Term.Var(rc.freshWild())(t.span)
    case Trees.Lit(l) => obj.Term.Lit(l)(t.span)
    case VarRef(n) =>
      sc.lookup(n) match
        case Some(s) if (s.kind == SymKind.MetaParam || s.kind == SymKind.MetaDef) && capturesVar(s) =>
          noteUse(t.span, s)
          syms.mtype(s).get match
            case Code(_) | Prim(_) => obj.Term.Splice(Ref(s))(t.span)
            case other =>
              err("E0202", s"meta variable `$n` cannot be used as a term", t.span, s"has meta type `${showMT(other)}`")
              obj.Term.Var(n)(t.span)
        case _ =>
          if !rc.allowVars then
            ctx.report(Diagnostic.error("E0201", "runtime value used at compile time", t.span, s"object variable `$n`")
              .withNote("object variables only exist inside rules, queries and formula functions"))
          obj.Term.Var(n)(t.span)
    case Trees.Neg(x) =>
      val e = elabTerm(x, sc, rc)
      e match
        case obj.Term.Splice(m) if isPrimMeta(m).isDefined => obj.Term.Splice(MExpr.Neg(m, t.span))(t.span)
        case _ => obj.Term.Neg(e)(t.span)
    case inf @ Infix(op, l, r) if ArithOp.fromString(op).isDefined =>
      val el = elabTerm(l, sc, rc)
      val er = elabTerm(r, sc, rc)
      val aop = ArithOp.fromString(op).get
      (stage1(el), stage1(er)) match
        case (Some(ml), Some(mr)) if !(el.isInstanceOf[obj.Term.Lit] && er.isInstanceOf[obj.Term.Lit]) =>
          // all operands are compile-time primitives: evaluated at stage 1 (Section 3.2, rule 3)
          val (bl, br) = (isPrimMeta(ml).get, isPrimMeta(mr).get)
          if bl != br || (aop == ArithOp.Concat) != (bl == BaseType.StringT) then
            err("E0203", s"operator `$op` cannot be applied to `${bl.show}` and `${br.show}`", inf.opSpan)
          obj.Term.Splice(Op(aop, ml, mr, t.span))(t.span)
        case _ => obj.Term.Arith(aop, el, er)(t.span)
    case Infix(op, _, _) =>
      err("E0202", s"`$op` is a formula, not a term", t.span, "expected a term")
      obj.Term.Var(rc.freshWild())(t.span)
    case As(x, v) =>
      obj.Term.As(elabTerm(x, sc, rc), v.name)(t.span)
    case Ascribe(x, tp) => obj.Term.Ascr(elabTerm(x, sc, rc), elabOType(tp, sc, TVars.NoTVars))(t.span)
    case With(v, fields) =>
      val vt = elabTerm(v, sc, rc)
      checkLabelsDistinct(fields.map(_.label))
      obj.Term.With(vt, fields.map(f => (f.label.name, elabTerm(f.value, sc, rc), f.label.span)))(t.span)
    case Select(q @ VarRef(n), l) if !sc.lookup(n).exists(capturesVar) =>
      obj.Term.Proj(elabTerm(q, sc, rc), l)(t.span)
    case Select(q @ VarRef(n), l) if sc.lookup(n).exists(s => syms.mtype(s).exists(_.isInstanceOf[Code])) =>
      obj.Term.Proj(elabTerm(q, sc, rc), l)(t.span)
    case _: Ident | _: Apply | _: Select =>
      val (head, args) = flattenApp(t)
      classify(head, sc, rc) match
        case Head.Obj(s) =>
          obj.Term.App(RelRef.Spliced(Ref(s)), elabArgs(s.name, relCols(s), args, sc, rc, t.span, isHead = false, s.span))(t.span)
        case Head.Meta(m, RelT(cols, _)) =>
          obj.Term.App(RelRef.Spliced(m), elabArgs(Printer.show(head), cols, args, sc, rc, t.span, isHead = false, Span.NoSpan))(t.span)
        case Head.Meta(m, mt @ (Code(_) | Prim(_))) =>
          if args.nonEmpty then
            err("E0207", s"`${Printer.show(head)}` is not a function", args.head.span, s"has meta type `${showMT(mt)}`")
          obj.Term.Splice(m)(t.span)
        case Head.Meta(m, pi: Pi) =>
          val (am, at) = elabApp(m, pi, args, sc, rc, t.span, head)
          at match
            case Code(_) | Prim(_) | MType.Err => obj.Term.Splice(am)(t.span)
            case PropT =>
              err("E0202", s"formula function `${Printer.show(head)}` used as a term", t.span, "this is a formula")
              obj.Term.Var(rc.freshWild())(t.span)
            case other =>
              err("E0202", "expected a term", t.span, s"this has meta type `${showMT(other)}`")
              obj.Term.Var(rc.freshWild())(t.span)
        case Head.Meta(_, MType.Err) => obj.Term.Var(rc.freshWild())(t.span)
        case Head.Meta(_, PropT) =>
          err("E0202", s"formula `${Printer.show(head)}` used as a term", t.span)
          obj.Term.Var(rc.freshWild())(t.span)
        case Head.Meta(_, other) =>
          ctx.report(Diagnostic.error("E0202", "expected a term", head.span, s"this has meta type `${showMT(other)}`")
            .withNote("only code (⇑τ), compile-time primitives and relations' facts can be used as terms"))
          obj.Term.Var(rc.freshWild())(t.span)
        case Head.ObjVar(n) =>
          if args.nonEmpty then err("E0207", s"variable `$n` cannot be applied to arguments", t.span)
          obj.Term.Var(n)(t.span)
        case Head.TypeLike(s) =>
          err("E0202", s"type `${s.name}` used as a term", head.span, "expected a term")
          obj.Term.Var(rc.freshWild())(t.span)
        case Head.Bad => obj.Term.Var(rc.freshWild())(t.span)
    case _: RecordLit =>
      err("E0202", "a record can only follow a relation (named pattern)", t.span)
      obj.Term.Var(rc.freshWild())(t.span)
    case other =>
      err("E0202", "expected a term", other.span)
      obj.Term.Var(rc.freshWild())(t.span)

  /** Fixes of a named pattern with missing labels: add them after the last field, in a body as `_` (or
   *  ignore them with `..`), in a head as variables named after the labels. */
  private def missingLabelFixes(d: Diagnostic, fields: List[Field], missing: List[String], isHead: Boolean): Diagnostic =
    fields.lastOption.fold(d) { last =>
      val at = last.value.span.endPoint
      val add = d.withSuggestion(
        "add the missing labels",
        at,
        missing.map(l => s", $l = ${if isHead then l.capitalize else "_"}").mkString
      )
      if isHead then add else add.withSuggestion("ignore the missing labels with `..`", at, ", ..")
    }

  private[meta] def checkLabelsDistinct(ls: List[Ident]): Unit =
    val seen = mutable.HashMap.empty[String, Span]
    for l <- ls do
      seen.get(l.name) match
        case Some(p) =>
          ctx.report(Diagnostic.error("E0307", s"duplicate label `${l.name}`", l.span, "duplicate").withLabel(p, "first used here"))
        case None => seen(l.name) = l.span

  /** Arguments of a relation atom / constructor term; named patterns are replaced by positional ones (Section 2.4). */
  private[meta] def elabArgs(
      rel: String,
      cols: List[Column],
      args: List[Tree],
      sc: Scope,
      rc: RuleCtx,
      span: Span,
      isHead: Boolean,
      declSpan: Span
  ): List[obj.Term] =
    args match
      case List(rl @ RecordLit(fields, rest)) if !(cols.length == 1 && cols.head.label.isEmpty) =>
        if rest && isHead then
          rc.failed = true
          ctx.report(Diagnostic.error("E0302", "`..` is not allowed in a rule head", rl.span, "rest pattern in head")
            .withNote("the omitted columns of a derived fact would be unknown"))
        checkLabelsDistinct(fields.map(_.label))
        val byLabel = fields.map(f => f.label.name -> f).toMap
        for f <- fields if !cols.exists(_.label.contains(f.label.name)) do
          rc.failed = true
          var d = Diagnostic.error("E0306", s"`$rel` has no column labelled `${f.label.name}`", f.label.span, "unknown label")
          val labels = cols.flatMap(_.label)
          if labels.isEmpty then d = d.withNote(s"the columns of `$rel` are not labelled")
          else d = d.withNote(s"labels of `$rel`: ${labels.mkString(", ")}")
          if declSpan.exists then d = d.withLabel(declSpan, "declared here")
          ctx.report(d)
        val missing = cols.flatMap(_.label).filterNot(byLabel.contains)
        if missing.nonEmpty && !rest && cols.forall(_.label.isDefined) then
          rc.failed = true
          val d = Diagnostic.error(
            "E0301",
            s"missing label${if missing.length > 1 then "s" else ""} in named pattern for `$rel`",
            rl.span,
            s"missing ${missing.map(l => s"`$l`").mkString(", ")}"
          )
            .withHelp(if isHead then s"add ${missing.map(l => s"`$l = ...`").mkString(", ")}"
            else "add the missing labels, or end the pattern with `..` to ignore them")
          ctx.report(missingLabelFixes(d, fields, missing, isHead))
        if cols.exists(_.label.isEmpty) then
          rc.failed = true
          err("E0306", s"`$rel` does not label all of its columns, so it cannot be used with a named pattern", rl.span)
        cols.map { c =>
          c.label.flatMap(byLabel.get) match
            case Some(f) => elabTerm(f.value, sc, rc)
            case None => obj.Term.Var(rc.freshWild())(rl.span)
        }
      case _ =>
        if args.length != cols.length then
          rc.failed = true
          var d = Diagnostic.error(
            "E0207",
            s"`$rel` expects ${cols.length} argument${if cols.length == 1 then "" else "s"}, found ${args.length}",
            span,
            s"${args.length} argument${if args.length == 1 then "" else "s"} given"
          )
          if declSpan.exists then d = d.withLabel(declSpan, "declared here")
          ctx.report(d)
        args.map(elabTerm(_, sc, rc))

  def elabFormula(t: Tree, sc: Scope, rc: RuleCtx): List[obj.Formula] = t match
    case Parens(i) => elabFormula(i, sc, rc)
    case Conj(l, r) => elabFormula(l, sc, rc) ++ elabFormula(r, sc, rc)
    case Disj(_, _) =>
      def alts(t: Tree): List[Tree] = t match
        case Disj(l, r) => alts(l) ++ alts(r)
        case Parens(i @ Disj(_, _)) => alts(i)
        case other => List(other)
      List(obj.Formula.Disj(alts(t).map(elabFormula(_, sc, rc)))(t.span))
    case Trees.Not(x) =>
      elabFormula(x, sc, rc) match
        case List(a: obj.Formula.Atom) =>
          checkCompleteParam(a.rel, a.span, "negates")
          List(obj.Formula.Not(a)(t.span))
        case List(_: obj.Formula.Splice) =>
          ctx.report(Diagnostic.error("E0202", "`not` applies only to relation atoms", x.span, "this is a formula function use")
            .withNote("formula functions may expand to arbitrary formulas; declare a relation for the negated condition"))
          Nil
        case Nil => Nil
        case _ =>
          err("E0202", "`not` applies only to relation atoms", x.span, "not a relation atom")
          Nil
    case Infix("=", VarRef(v), agg @ Agg(kind, term, body)) =>
      val res = VarRef(v)(t.span)
      rc.aggDepth += 1
      val b =
        try elabFormula(body, sc, rc)
        finally rc.aggDepth -= 1
      for case a: obj.Formula.Atom <- b do checkCompleteParam(a.rel, a.span, "aggregates over")
      List(obj.Formula.Agg(v, kind, elabTerm(term, sc, rc), b)(t.span))
    case Infix(op, l, r) if CmpOp.fromString(op).isDefined =>
      if r.isInstanceOf[Agg] || l.isInstanceOf[Agg] then
        err("E0202", "an aggregate must be bound to a variable, `X = count { ... }`", t.span)
        Nil
      else List(obj.Formula.Cmp(CmpOp.fromString(op).get, elabTerm(l, sc, rc), elabTerm(r, sc, rc))(t.span))
    case As(inner, v) =>
      elabFormula(inner, sc, rc) match
        case List(a: obj.Formula.Atom) if a.as.isEmpty => List(obj.Formula.Atom(a.rel, a.args, Some(v.name))(t.span))
        case _ =>
          err("E0202", "`as` in a body applies to a relation atom", t.span)
          Nil
    case _: Ident | _: Apply | _: Select | _: VarRef =>
      val (head, args) = flattenApp(t)
      classify(head, sc, rc) match
        case Head.Obj(s) =>
          List(obj.Formula.Atom(RelRef.Spliced(Ref(s)), elabArgs(s.name, relCols(s), args, sc, rc, t.span, isHead = false, s.span), None)(
            t.span
          ))
        case Head.Meta(m, RelT(cols, _)) =>
          List(obj.Formula.Atom(
            RelRef.Spliced(m),
            elabArgs(Printer.show(head), cols, args, sc, rc, t.span, isHead = false, Span.NoSpan),
            None
          )(t.span))
        case Head.Meta(m, PropT) =>
          if args.nonEmpty then err("E0207", s"`${Printer.show(head)}` is a formula, not a function", args.head.span)
          List(obj.Formula.Splice(m)(t.span))
        case Head.Meta(m, pi: Pi) =>
          val (am, at) = elabApp(m, pi, args, sc, rc, t.span, head)
          at match
            case PropT =>
              val bodySpan = head match
                case Ident(n) => sc.lookup(n).flatMap(_.decl).map(_.span).getOrElse(Span.NoSpan)
                case _ => Span.NoSpan
              rc.expansions += Expansion(Printer.show(head), t.span, bodySpan)
              List(obj.Formula.Splice(am)(t.span))
            case MType.Err => Nil
            case Pi(_, _, _, _) =>
              ctx.report(Diagnostic.error(
                "E0207",
                s"formula function `${Printer.show(head)}` is not fully applied",
                t.span,
                "missing arguments"
              )
                .withNote(s"`${Printer.show(head)}` has meta type `${showMT(pi)}`"))
              Nil
            case other =>
              err("E0202", "expected a formula", t.span, s"this has meta type `${showMT(other)}`")
              Nil
        case Head.Meta(_, MType.Err) | Head.Bad => Nil
        case Head.Meta(_, other) =>
          ctx.report(Diagnostic.error("E0202", "expected a formula", head.span, s"this has meta type `${showMT(other)}`")
            .withNote("a formula is a relation atom, a comparison, an aggregate or a formula function use"))
          Nil
        case Head.ObjVar(n) =>
          err("E0202", "expected a formula", t.span, s"variable `$n` is not a formula")
          Nil
        case Head.TypeLike(s) =>
          ctx.report(Diagnostic.error("E0202", "expected a formula", head.span, s"`${s.name}` is a type, not a relation")
            .withHelp(s"to test membership in a type, write an ascription `(X : ${s.name})` inside an atom"))
          Nil
    case other =>
      err("E0202", "expected a formula", other.span, "not a formula")
      Nil

  /** A functor that negates or aggregates over a relation parameter must require %complete (Section 11). */
  private[meta] def checkCompleteParam(r: RelRef, span: Span, what: String): Unit = r match
    case RelRef.Spliced(Proj(Ref(p), l)) if p.kind == SymKind.MetaParam =>
      syms.mtype(p) match
        case Some(Sig(_, reqs)) if !reqs.exists { case Req.Complete(`l`, _) => true; case _ => false } =>
          ctx.report(Diagnostic.error(
            "E0210",
            s"the functor $what the relation parameter `${p.name}.$l` without requiring `%complete $l`",
            span,
            s"`${p.name}.$l` may be bound to an incomplete relation"
          )
            .withLabel(p.span, s"parameter `${p.name}` declared here")
            .withHelp(s"add `%complete $l` to the signature of `${p.name}`")
            .pipe(d =>
              signatureOf(p).flatMap(_.entries.lastOption).fold(d) { last =>
                val end = last match
                  case SigEntry.FieldDecl(_, tpe) => tpe.span
                  case SigEntry.Complete(_, sp) => sp
                  case SigEntry.ModeReq(_, _, sp) => sp
                d.withSuggestion(s"add `%complete $l`", end.endPoint, s", %complete $l")
              }
            ))
        case _ =>
    case RelRef.Spliced(Ref(p)) if p.kind == SymKind.MetaParam =>
      // a relation parameter `(r : A -> rel)` cannot carry requirements
      ctx.report(Diagnostic.error(
        "E0210",
        s"the function $what the relation parameter `${p.name}`",
        span,
        s"`${p.name}` may be bound to an incomplete relation"
      )
        .withLabel(p.span, s"parameter `${p.name}` declared here")
        .withHelp("pass the relation in a signature with `%complete`, e.g. `(m : { r : A -> rel, %complete r })`"))
    case _ =>

  /** The signature a meta parameter was declared with, as written: a record type in the parameter, or the
   *  definition of the named signature. */
  private def signatureOf(p: Sym): Option[RecordType] =
    syms.paramType(p).flatMap {
      case rt: RecordType => Some(rt)
      case Ident(n) => p.owner.lookup(n).flatMap(_.decl).collect { case Decl(_, _, _, _, Some(rt: RecordType), _) => rt }
      case _ => None
    }

  def elabHead(t: Tree, sc: Scope, rc: RuleCtx): Option[obj.Term] =
    val (head, args) = flattenApp(t)
    classify(head, sc, rc) match
      case Head.Obj(s) =>
        Some(obj.Term.App(RelRef.Spliced(Ref(s)), elabArgs(s.name, relCols(s), args, sc, rc, t.span, isHead = true, s.span))(t.span))
      case Head.Meta(m, RelT(cols, _)) =>
        Some(obj.Term.App(RelRef.Spliced(m), elabArgs(Printer.show(head), cols, args, sc, rc, t.span, isHead = true, Span.NoSpan))(t.span))
      case Head.Bad | Head.Meta(_, MType.Err) => None
      case Head.Meta(_, PropT) | Head.Meta(_, _: Pi) =>
        ctx.report(Diagnostic.error("E0103", "the head of a rule must be a relation", head.span, "formula function")
          .withNote("clauses of a formula function must be in the same scope as its declaration"))
        None
      case _ =>
        ctx.report(Diagnostic.error("E0103", "the head of a rule must be a relation atom", t.span, "not a relation atom")
          .withNote("rules have the form `c t1 ... tn :- body.` where `c` is a relation"))
        None
