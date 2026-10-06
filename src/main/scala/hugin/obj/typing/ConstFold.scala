package hugin.obj
package typing

import hugin.util.*
import hugin.compiler.*
import hugin.syntax.Literal

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

  def start(using Context): MiniPhase.Transformer = Folder

  /** Stateless: one transformer serves every traversal. */
  private object Folder extends MiniPhase.Transformer:
    override def transformRule(r: Rule)(using Context): List[Rule] =
      val warn = (d: Diagnostic) => ctx.report(Diag.rule(r)(d))
      List(r.withParts(heads = r.heads.map(fold(_, warn)), body = r.body.map(foldF(_, warn))))
    override def transformQuery(q: Query)(using Context): Query =
      q.withBody(q.body.map(foldF(_, d => ctx.report(Diag.query(q)(d)))))
