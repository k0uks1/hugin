package hugin.core
package handover

import hugin.obj
import hugin.obj.{Formula, RelRef, Term}
import hugin.core.elab.ElabProblem
import hugin.util.*
import hugin.util.diagnostics.Problem

/** Thrown when staged object code does not have the shape of an object item; the item is dropped. */
final class NotObjectCode(val diagnostic: Diagnostic) extends Exception(diagnostic.message, null, false, false)

/** Translates the staged object code of one item (normal forms over the item's variables `names`,
 *  innermost first) into object terms and formulas (`obj.Trees`). Every object node gets the position of
 *  the nearest enclosing [[ObjForm.Loc]]; wildcards become fresh variables (`_#1`, `_#2`, … per item, in
 *  order of occurrence, as the object level expects). */
final class ObjectTerms(core: Core, symbols: ObjectSymbols, names: List[Name], itemSpan: Span):
  import core.*

  private var wild = 0
  private def freshWild(): String =
    wild += 1
    s"${obj.Var.WildPrefix}$wild"

  private def bad(problem: Problem): Nothing = throw NotObjectCode(problem.toDiagnostic)

  private def expected(what: String, t: Tm, span: Span): Nothing = bad(ElabProblem.NotObjectShape(what, showTmBounded(names, t), span))

  private def variable(t: Tm, span: Span): String = Tm.unloc(t) match
    case Tm.Var(ix) => names(ix)
    case Tm.Obj(ObjForm.Named(x), Nil) => x
    case Tm.Obj(ObjForm.Wild, Nil) => freshWild()
    case other => expected("a variable", other, span)

  /** The relation, constructor or struct `t` refers to. */
  private def relation(t: Tm, span: Span): obj.RelSym = Tm.unloc(t) match
    case Tm.Global(id) => symbols.relSym(id).getOrElse(expected("a relation", t, span))
    case other => expected("a relation", other, span)

  private def spine(t: Tm, args: List[Tm]): (Tm, List[Tm]) = Tm.unloc(t) match
    case Tm.App(f, a, _) => spine(f, a :: args)
    case other => (other, args)

  def term(t: Tm, span: Span = itemSpan): Term = t match
    case Tm.Obj(ObjForm.Loc(sp), List(u)) => term(u, sp)
    case Tm.Var(ix) => Term.Var(names(ix))(span)
    case Tm.Obj(ObjForm.Named(x), Nil) => Term.Var(x)(span)
    case Tm.Lit(l, _) => Term.Lit(l)(span)
    case Tm.Arith(op, a, b, _) => Term.Arith(op, term(a, span), term(b, span))(span)
    case Tm.Negate(a, _) => Term.Neg(term(a, span))(span)
    case Tm.Obj(ObjForm.Wild, Nil) => Term.Var(freshWild())(span)
    case Tm.Obj(ObjForm.As, List(a, x)) =>
      val inner = term(a, span)
      Term.As(inner, variable(x, span))(span)
    case Tm.Obj(ObjForm.Ascribe, List(a, ty)) =>
      val inner = term(a, span)
      Term.Ascr(inner, symbols.otype(ty, span))(span)
    case Tm.Obj(ObjForm.Proj(l), List(a)) => Term.Proj(term(a, span), l)(span)
    case Tm.Obj(ObjForm.With(ls), a :: es) =>
      val inner = term(a, span)
      Term.With(inner, ls.zip(es).map { case ((l, lsp), e) => (l, term(e, span), lsp) })(span)
    case Tm.App(_, _, _) | Tm.Global(_) =>
      val (head, args) = spine(t, Nil)
      recordInstance(head, span)
      Term.App(RelRef.Sym(relation(head, span)), args.map(term(_, span)))(span)
    case other => expected("an object term", other, span)

  /** A use of a family instance (`cons[int]`) at `span`, for tooling (hover over the family's name). */
  private def recordInstance(head: Tm, span: Span): Unit = Tm.unloc(head) match
    case Tm.Global(id) =>
      globals(id).instanceOf.foreach((fam, _) => symbols.index.instance(globals(fam).span, globals(id).name, span))
    case _ =>

  def formulas(t: Tm, span: Span = itemSpan): List[Formula] = t match
    case Tm.Obj(ObjForm.Loc(sp), List(u)) => formulas(u, sp)
    case Tm.Obj(ObjForm.And, as) => as.flatMap(formulas(_, span))
    case Tm.Obj(ObjForm.Or, _) => List(Formula.Disj(alternatives(t).map(formulas(_, span)))(span))
    case Tm.Obj(ObjForm.Not, List(a)) =>
      formulas(a, span) match
        case List(atom: Formula.Atom) => List(Formula.Not(atom)(span))
        case _ => bad(ElabProblem.NotAnAtom("not", spanOf(a, span)))
    case Tm.Obj(ObjForm.Compare(op), List(a, b)) => List(Formula.Cmp(op, term(a, span), term(b, span))(span))
    case Tm.Obj(ObjForm.Agg(kind), List(x, a, b)) =>
      val res = variable(x, span)
      val inner = term(a, span)
      List(Formula.Agg(res, kind, inner, formulas(b, span))(span))
    case Tm.Obj(ObjForm.As, List(a, x)) =>
      formulas(a, span) match
        case List(atom: Formula.Atom) if atom.as.isEmpty => List(Formula.Atom(atom.rel, atom.args, Some(variable(x, span)))(span))
        case _ => bad(ElabProblem.NotAnAtom("as", span))
    case Tm.App(_, _, _) | Tm.Global(_) =>
      val (head, args) = spine(t, Nil)
      recordInstance(head, span)
      List(Formula.Atom(RelRef.Sym(relation(head, span)), args.map(term(_, span)), None)(span))
    case other => expected("a formula", other, span)

  /** The alternatives of nested disjunctions (`a ; (b ; c)` has three). */
  private def alternatives(t: Tm): List[Tm] = Tm.unloc(t) match
    case Tm.Obj(ObjForm.Or, as) => as.flatMap(alternatives)
    case _ => List(t)

  private def spanOf(t: Tm, default: Span): Span = t match
    case Tm.Obj(ObjForm.Loc(sp), _) => sp
    case _ => default
