package hugin.obj
package check

import hugin.util.*
import hugin.obj.typing.Moding

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

  /** The constructor subterms of a term (every constructor is a fact constructor). */
  def factTerms(t: Term): List[Term.App] = t match
    case a @ Term.App(_, as) => a :: as.flatMap(factTerms)
    case Term.As(x, _) => factTerms(x)
    case Term.Ascr(x, _) => factTerms(x)
    case Term.Arith(_, l, r) => factTerms(l) ++ factTerms(r)
    case Term.Neg(x) => factTerms(x)
    case _ => Nil

  /** (relation, negative?, span) for every relation whose facts a body reads (`bound`: the variables bound
   *  before it): the relations of its atoms, and the fact-constructor terms of the value side of binding
   *  equations, which are existence checks (`X = c t̄` reads as `(c t̄ as X)`). Constructor patterns nested
   *  in atoms or on the pattern side of an equation match values structurally, and comparisons and
   *  aggregate terms are structural (reference: object/facts): they read no facts.
   *  Which side of an equation binds follows the canonical order (Lemma 6.4); if the body has none (it is
   *  ill-moded, reported elsewhere), every fact-constructor term of an equation counts. */
  def occurrences(body: List[Formula], neg: Boolean = false, bound: Set[String] = Set.empty): List[(RelSym, Boolean, Span)] =
    val (ordered, moded) = Moding.canonical(body, bound) match
      case Right((o, _)) => (o, true)
      case Left(_) => (body, false)
    var b = bound
    ordered.flatMap { f =>
      val out = f match
        case a @ Formula.Atom(r, _, _) => List((r.sym, neg, a.span))
        case n @ Formula.Not(a) => List((a.rel.sym, true, n.span))
        case Formula.Agg(_, _, _, ib) => occurrences(ib, neg = true, b).map((r, _, s) => (r, true, s))
        case c @ Formula.Cmp(CmpOp.Eq, l, r) =>
          val lb = Moding.vars(l).subsetOf(b)
          val rb = Moding.vars(r).subsetOf(b)
          val values = if !moded then List(l, r) else if lb && rb then Nil else if rb then List(r) else List(l)
          values.flatMap(factTerms).map(t => (t.rel.sym, neg, c.span))
        case Formula.Disj(alts) => alts.flatMap(occurrences(_, neg, b))
        case _ => Nil
      b = Moding.step(f, b).getOrElse(b ++ Moding.formulaVars(f))
      out
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

  /** Constructor terms strictly inside the head's arguments that are not matched in the body: the terms a
   *  rule builds (for termination, Definition 10.1). With `withHead`, the head itself counts too
   *  if its relation is a fact constructor or fact struct: its fact is a term, so a rule `s (s N) :- s N`
   *  builds `s (s N)` although its argument is matched (a split rule of Proposition 8.8 has this shape,
   *  see `StratifyPhase.splitRules`). */
  def newHeadConstructors(r: Rule, withHead: Boolean = false): List[Term.App] =
    val existing = positiveSubpatterns(r.body)
    def inner(t: Term): List[Term.App] = t match
      case a @ Term.App(_, as) => (if existing(a) then Nil else List(a)) ++ as.flatMap(inner)
      case Term.As(x, _) => inner(x)
      case Term.Ascr(x, _) => inner(x)
      case Term.Arith(_, l, rr) => inner(l) ++ inner(rr)
      case Term.Neg(x) => inner(x)
      case _ => Nil
    r.heads.flatMap {
      case a @ Term.App(RelRef.Sym(c), _) if withHead && isFactCtor(c) => inner(a)
      case Term.App(_, as) => as.flatMap(inner)
      case _ => Nil
    }

  /** A fact constructor or fact struct: a relation whose facts are constructor terms. */
  def isFactCtor(c: RelSym): Boolean = c.isCtor || c.kind == RelKind.Struct

  /** The fact-constructor terms a rule's head asserts besides its own fact (`subfact_F`): the constructor
   *  terms of its arguments that the body does not match. */
  def assertedHeadConstructors(r: Rule): List[Term.App] = newHeadConstructors(r)

  def edges(p: ObjProgram)(using ProgramFacts): List[DepEdge] =
    p.rules.toList.flatMap { r =>
      val heads = r.heads.collect { case Term.App(RelRef.Sym(c), _) => c }
      val occ = occurrences(r.body)
      val ctors = assertedHeadConstructors(r).map(_.rel.sym).distinct
      val fromHead = for h <- heads; (o, neg, sp) <- occ yield DepEdge(h, o, neg, sp, r)
      val fromCtors = for c <- ctors; (o, neg, sp) <- occ yield DepEdge(c, o, neg, sp, r)
      fromHead ++ fromCtors
    }
