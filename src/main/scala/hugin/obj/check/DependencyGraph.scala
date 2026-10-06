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

  /** Every relation a formula mentions: its atoms and all constructor terms, also nested patterns. */
  def mentioned(f: Formula): List[RelSym] = f match
    case Formula.Atom(r, args, _) => r.sym :: args.flatMap(relsIn)
    case Formula.Not(a) => mentioned(a)
    case Formula.Agg(_, _, t, b) => relsIn(t) ++ b.flatMap(mentioned)
    case Formula.Disj(alts) => alts.flatten.flatMap(mentioned)
    case Formula.Cmp(_, l, r) => relsIn(l) ++ relsIn(r)
    case _ => Nil

  /** (relation, negative?, span) for every relation whose facts a body reads: the relations of its atoms.
   *  Constructor patterns nested in atoms match values structurally and read no facts (see [[Probes]]);
   *  constructor terms compared with `=` or `<>` must exist as values, so they count. */
  def occurrences(body: List[Formula], neg: Boolean = false): List[(RelSym, Boolean, Span)] = body.flatMap {
    case a @ Formula.Atom(r, _, _) => List((r.sym, neg, a.span))
    case n @ Formula.Not(a) => List((a.rel.sym, true, n.span))
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

  /** Constructor terms strictly inside the head's arguments that do not already exist in the body
   *  (probes included: they are new values, see [[Probes]]). */
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
      // facts asserted by the head: constructors built outside its probe columns
      val probeCols = Probes.columns(r)
      val asserting = r.withParts(heads = r.heads.map {
        case a @ Term.App(c, as) => Term.App(c, as.zipWithIndex.filterNot((_, i) => probeCols(i)).map(_._1))(a.span)
        case other => other
      })
      val ctors = newHeadConstructors(asserting).map(_.rel.sym).distinct
      val fromHead = for h <- heads; (o, neg, sp) <- occ yield DepEdge(h, o, neg, sp, r)
      val fromCtors = for c <- ctors; (o, neg, sp) <- occ yield DepEdge(c, o, neg, sp, r)
      fromHead ++ fromCtors
    }
