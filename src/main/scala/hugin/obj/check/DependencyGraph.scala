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
    case _ => Nil

  /** The fact-constructor subterms of a term (descending through data and fact constructors). */
  def factTerms(t: Term): List[Term.App] = t match
    case a @ Term.App(r, as) => (if r.sym.isData then Nil else List(a)) ++ as.flatMap(factTerms)
    case Term.As(x, _) => factTerms(x)
    case Term.Ascr(x, _) => factTerms(x)
    case Term.Arith(_, l, r) => factTerms(l) ++ factTerms(r)
    case Term.Neg(x) => factTerms(x)
    case _ => Nil

  /** (relation, negative?, span) for every relation whose facts a body reads (`bound`: the variables bound
   *  before it): the relations of its atoms, and the fact-constructor terms of the value side of binding
   *  equations, which are existence checks (`X = c t̄` reads as `(c t̄ as X)`). Constructor patterns nested
   *  in atoms or on the pattern side of an equation match values structurally, and comparisons and
   *  aggregate terms are structural (see docs/NOTES.md, "Data and fact constructors"): they read no facts.
   *  Which side of an equation binds follows the canonical order (Lemma 6.4); if the body has none (it is
   *  ill-moded, reported elsewhere), every fact-constructor term of an equation counts. */
  def occurrences(body: List[Formula], neg: Boolean = false, bound: Set[String] = Set.empty)(using
      ProgramFacts
  ): List[(RelSym, Boolean, Span)] =
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

  /** Constructor terms (data and fact) strictly inside the head's arguments that are not matched in the
   *  body: the terms a rule builds (for termination, Definition 10.1). The heads of demand rules are the
   *  inputs of moded calls, so terms built there count too. */
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

  /** The input columns of the head of a rule of a moded relation guarded by the demand of mode `m` (by
   *  the demand transformation): they are patterns, matched against the demand, not constructions. Their
   *  fact-constructor subterms are facts already (no moded input builds one, E0504), so asserting them
   *  again adds nothing. */
  def guardedInputs(r: Rule): Set[Int] =
    r.heads.headOption match
      case Some(Term.App(RelRef.Sym(h), _)) =>
        r.body
          .collectFirst { case Formula.Atom(RelRef.Sym(d), _, _) if d.isDemand => d.kind }
          .collect { case RelKind.Demand(`h`, m) => m.inputs.zipWithIndex.collect { case (true, i) => i }.toSet }
          .getOrElse(Set.empty)
      case _ => Set.empty

  /** The fact-constructor terms a rule's head asserts besides its own fact (`subfact_F`): new fact terms
   *  outside the guarded input columns. Data constructors never assert. */
  def assertedHeadConstructors(r: Rule): List[Term.App] =
    val guarded = guardedInputs(r)
    val asserting = r.withParts(heads = r.heads.map {
      case a @ Term.App(c, as) => Term.App(c, as.zipWithIndex.filterNot((_, i) => guarded(i)).map(_._1))(a.span)
      case other => other
    })
    newHeadConstructors(asserting).filterNot(_.rel.sym.isData)

  def edges(p: ObjProgram)(using ProgramFacts): List[DepEdge] =
    p.rules.toList.flatMap { r =>
      val heads = r.heads.collect { case Term.App(RelRef.Sym(c), _) => c }
      val occ = occurrences(r.body)
      val ctors = assertedHeadConstructors(r).map(_.rel.sym).distinct
      val fromHead = for h <- heads; (o, neg, sp) <- occ yield DepEdge(h, o, neg, sp, r)
      val fromCtors = for c <- ctors; (o, neg, sp) <- occ yield DepEdge(c, o, neg, sp, r)
      fromHead ++ fromCtors
    }
