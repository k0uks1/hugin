package hugin.obj
package check

import hugin.util.*

/** An edge of the dependency graph (Section 6.4): `from` depends on `to`. */
final case class DepEdge(from: RelSym, to: RelSym, negative: Boolean, span: Span, rule: Rule)

object DepGraph:
  /** Relations occurring in a term (constructor patterns). */
  def relsIn(t: Term): List[RelSym] = t match
    case Term.App(r, as) => r.sym :: as.flatMap(relsIn)
    case Term.As(x, _) => relsIn(x)
    case Term.Ascr(x, _) => relsIn(x)
    case Term.Arith(_, l, r) => relsIn(l) ++ relsIn(r)
    case Term.Neg(x) => relsIn(x)
    case _ => Nil

  /** (relation, negative?, span) for every occurrence in a body. */
  def occurrences(body: List[Formula], neg: Boolean = false): List[(RelSym, Boolean, Span)] = body.flatMap {
    case a @ Formula.Atom(r, as, _) => (r.sym, neg, a.span) :: as.flatMap(relsIn).map(x => (x, neg, a.span))
    case n @ Formula.Not(a) => (a.rel.sym, true, n.span) :: a.args.flatMap(relsIn).map(x => (x, true, n.span))
    case g @ Formula.Agg(_, _, t, b) => relsIn(t).map(x => (x, true, g.span)) ++ occurrences(b, neg = true).map((r, _, s) => (r, true, s))
    case c @ Formula.Cmp(_, l, r) => (relsIn(l) ++ relsIn(r)).map(x => (x, neg, c.span))
    case Formula.Disj(alts) => occurrences(alts.flatten, neg)
    case _ => Nil
  }

  /** Constructor subpatterns of positive body atoms (the atoms themselves included). */
  def positiveSubpatterns(body: List[Formula]): Set[Term] =
    def subs(t: Term): List[Term] = t match
      case a @ Term.App(_, as) => a :: as.flatMap(subs)
      case Term.As(x, _) => subs(x)
      case Term.Ascr(x, _) => subs(x)
      case _ => Nil
    body.flatMap {
      case a @ Formula.Atom(r, as, _) => Term.App(r, as)(a.span) :: as.flatMap(subs)
      case _ => Nil
    }.toSet

  /** Constructor terms strictly inside the head's arguments that do not already exist in the body. */
  def newHeadConstructors(r: Rule): List[Term.App] =
    val existing = positiveSubpatterns(r.body)
    def inner(t: Term): List[Term.App] = t match
      case a @ Term.App(_, as) => (if existing(a) then Nil else List(a)) ++ as.flatMap(inner)
      case Term.As(x, _) => inner(x)
      case Term.Ascr(x, _) => inner(x)
      case Term.Arith(_, l, rr) => inner(l) ++ inner(rr)
      case Term.Neg(x) => inner(x)
      case _ => Nil
    r.heads.flatMap {
      case Term.App(_, as) => as.flatMap(inner)
      case _ => Nil
    }

  def edges(p: ObjProgram): List[DepEdge] =
    p.rules.toList.flatMap { r =>
      val heads = r.heads.collect { case Term.App(RelRef.Sym(c), _) => c }
      val occ = occurrences(r.body)
      val ctors = newHeadConstructors(r).map(_.rel.sym).distinct
      val fromHead = for h <- heads; (o, neg, sp) <- occ yield DepEdge(h, o, neg, sp, r)
      val fromCtors = for c <- ctors; (o, neg, sp) <- occ yield DepEdge(c, o, neg, sp, r)
      fromHead ++ fromCtors
    }
