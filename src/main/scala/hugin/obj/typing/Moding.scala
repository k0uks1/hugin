package hugin.obj
package typing

import hugin.util.*
import hugin.compiler.*
import scala.collection.mutable

/** Binding steps, canonical order and range restriction (Section 6.3). */
object Moding:
  def vars(t: Term): Set[String] = t match
    case Term.Var(n) => Set(n)
    case Term.App(_, as) => as.flatMap(vars).toSet
    case Term.As(x, v) => vars(x) + v
    case Term.Ascr(x, _) => vars(x)
    case Term.Proj(v, _) => vars(v)
    case Term.With(v, fs) => vars(v) ++ fs.flatMap(f => vars(f._2))
    case Term.Arith(_, l, r) => vars(l) ++ vars(r)
    case Term.Neg(x) => vars(x)
    case _ => Set.empty

  /** Variables that must be bound before a term can be matched at an unbound position:
   *  those under arithmetic, projections and updates (which count as uses with mode +). */
  def needs(t: Term): Set[String] = t match
    case Term.Var(_) | Term.Lit(_) => Set.empty
    case Term.App(_, as) => as.flatMap(needs).toSet
    case Term.As(x, _) => needs(x)
    case Term.Ascr(x, _) => needs(x)
    case other => vars(other)

  def formulaVars(f: Formula): Set[String] = f match
    case Formula.Atom(_, as, v) => as.flatMap(vars).toSet ++ v
    case Formula.Cmp(_, l, r) => vars(l) ++ vars(r)
    case Formula.Not(_) => Set.empty
    case Formula.Agg(res, _, _, _) => Set(res)
    case Formula.Disj(alts) => alts.map(_.flatMap(formulaVars).toSet).reduceOption(_ intersect _).getOrElse(Set.empty)

  def applicable(m: Mode, args: List[Term], b: Set[String]): Boolean =
    m.inputs.zip(args).forall((in, a) => if in then vars(a).subsetOf(b) else needs(a).subsetOf(b))

  def firstApplicable(c: RelSym, args: List[Term], b: Set[String])(using facts: ProgramFacts): Option[Mode] =
    facts.modesOf(c).find(applicable(_, args, b))

  /** Why a formula cannot take a binding step. */
  enum Stuck:
    case NoMode(a: Formula.Atom, b: Set[String])
    case Unbound(f: Formula, missing: Set[String])
    case Inner(f: Formula, inner: Stuck)

  /** B ⊢ φ ⇒ B' (Definition 6.3). */
  def step(f: Formula, b: Set[String])(using facts: ProgramFacts): Either[Stuck, Set[String]] = f match
    case Formula.Atom(RelRef.Sym(c), _, Some(v)) if c.isData =>
      // a generated guard `(c Z̄ as X)` over a data constructor destructures the bound value of `X`
      // (a data constructor has no facts to enumerate)
      if b(v) then Right(b ++ formulaVars(f)) else Left(Stuck.Unbound(f, Set(v)))
    case a @ Formula.Atom(RelRef.Sym(c), args, v) =>
      if firstApplicable(c, args, b).isDefined then Right(b ++ formulaVars(f))
      else Left(Stuck.NoMode(a, b))
    case Formula.Cmp(CmpOp.Eq, l, r) =>
      val lb = vars(l).subsetOf(b)
      val rb = vars(r).subsetOf(b)
      def isPattern(t: Term) = t match
        case Term.Var(_) | Term.App(_, _) | Term.As(_, _) => needs(t).subsetOf(b)
        case _ => false
      if (lb && rb) || (rb && isPattern(l)) || (lb && isPattern(r)) then Right(b ++ vars(l) ++ vars(r))
      else Left(Stuck.Unbound(f, (vars(l) ++ vars(r)) -- b))
    case Formula.Cmp(_, l, r) =>
      val all = vars(l) ++ vars(r)
      if all.subsetOf(b) then Right(b) else Left(Stuck.Unbound(f, all -- b))
    case Formula.Not(a @ Formula.Atom(RelRef.Sym(c), args, _)) =>
      val local = args.flatMap(vars).toSet -- b
      if !args.forall(x => needs(x).subsetOf(b)) then Left(Stuck.Unbound(f, args.flatMap(needs).toSet -- b))
      else if facts.hasModes(c) && firstApplicable(c, args, b).isEmpty then Left(Stuck.NoMode(a, b))
      else Right(b)
    case Formula.Agg(res, _, t, body) =>
      canonical(body, b) match
        case Right((_, b2)) =>
          if vars(t).subsetOf(b2) then Right(b + res)
          else Left(Stuck.Unbound(f, vars(t) -- b2))
        case Left(s) => Left(Stuck.Inner(f, s))
    case Formula.Disj(alts) =>
      val results = alts.map(canonical(_, b))
      results.collectFirst { case Left(s) => s } match
        case Some(s) => Left(Stuck.Inner(f, s))
        case None => Right(results.collect { case Right((_, b2)) => b2 }.reduceOption(_ intersect _).getOrElse(b))
    case _ => Right(b)

  /** Greedy canonical order (Lemma 6.4): repeatedly pick the leftmost formula that can step. */
  def canonical(body: List[Formula], b0: Set[String])(using ProgramFacts): Either[Stuck, (List[Formula], Set[String])] =
    var rest = body
    var b = b0
    val out = mutable.ListBuffer.empty[Formula]
    while rest.nonEmpty do
      val idx = rest.indexWhere(f => step(f, b).isRight)
      if idx < 0 then
        return Left(rest.map(f => step(f, b)).collectFirst { case Left(s) => s }.get)
      val f = rest(idx)
      b = step(f, b).toOption.get
      out += f
      rest = rest.patch(idx, Nil, 1)
    Right((out.toList, b))

  def headInputVars(h: Term, m: Mode): Set[String] = h match
    case Term.App(_, args) => args.zip(m.inputs).filter(_._2).flatMap((a, _) => vars(a)).toSet
    case _ => Set.empty

  def describe(s: Stuck)(using ProgramFacts): Diagnostic = problem(s).toDiagnostic

  /** Why the canonical order got stuck. */
  def problem(s: Stuck)(using facts: ProgramFacts): ModingError = s match
    case Stuck.NoMode(a, b) =>
      val c = a.rel.sym
      val modes = facts.modesOf(c)
      val unboundInputs = modes.map(m =>
        a.args.zip(m.inputs).zipWithIndex.collect {
          case ((t, true), i) if !vars(t).subsetOf(b) => (i, vars(t) -- b)
        }
      )
      val best = unboundInputs.minBy(_.length)
      ModingError.NoApplicableMode(c, a.span, modes, best.map(_._1), best.flatMap(_._2).distinct.map(VarName(_)))
    case Stuck.Unbound(f, missing) =>
      val site = f match
        case Formula.Cmp(CmpOp.Eq, _, _) => UnboundSite.Equation
        case Formula.Cmp(_, _, _) => UnboundSite.Comparison
        case Formula.Agg(_, _, _, _) => UnboundSite.Aggregate
        case Formula.Not(_) => UnboundSite.Negation
        case _ => UnboundSite.Other
      ModingError.UnboundInFormula(missing.toList.sorted.map(VarName(_)), site, f.span)
    case Stuck.Inner(_, inner) => problem(inner)

/** Phase: range restriction and moding of every rule and query (Definitions 6.3–6.5). */
final class ModingPhase extends Phase:
  def phaseName = "moding"
  def description = "check range restriction and applicable modes"
  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val facts = ctx.unit.facts
    // input positions of the heads of moded relations must be patterns (Section 7.3)
    def isPattern(t: Term): Boolean = t match
      case Term.Var(_) | Term.Lit(_) => true
      case Term.App(_, as) => as.forall(isPattern)
      case _ => false
    p.rules = p.rules.filter { r =>
      var ok = true
      for h <- r.heads do
        h match
          case Term.App(RelRef.Sym(c), args) =>
            for (m, _) <- facts.modes(c); case ((a, true), i) <- args.zip(m.inputs).zipWithIndex if !isPattern(a) && ok do
              ok = false
              ctx.report(Diag.rule(r)(ModingError.HeadInputNotPattern(c, i, m, a.span).toDiagnostic))
            if ok then
              for m <- facts.modesOf(c) if ok do
                val b0 = Moding.headInputVars(h, m)
                Moding.canonical(r.body, b0) match
                  case Left(stuck) =>
                    ok = false
                    val p = Moding.problem(stuck)
                    ctx.report(Diag.rule(r)((if facts.hasModes(c) then p.checking(m, c) else p).toDiagnostic))
                  case Right((_, b)) =>
                    val headVars = r.heads.flatMap(Moding.vars).toSet
                    val missing = headVars -- b
                    if missing.nonEmpty then
                      ok = false
                      val spans = r.heads.flatMap(collectVarSpans(_, missing))
                      val checking = Option.when(facts.hasModes(c))((m, c))
                      val vs = missing.toList.sorted.map(VarName(_))
                      val p = ModingError.NotRangeRestricted(vs, spans.headOption.getOrElse(h.span), spans.drop(1), checking)
                      ctx.report(Diag.rule(r)(p.toDiagnostic))
          case _ => ok = false
      ok
    }
    p.queries = p.queries.filter { q =>
      Moding.canonical(q.body, Set.empty) match
        case Left(stuck) => ctx.report(Diag.query(q)(Moding.describe(stuck))); false
        case Right(_) => true
    }

  private def collectVarSpans(t: Term, vs: Set[String]): List[Span] = t match
    case v @ Term.Var(n) if vs(n) => List(v.span)
    case Term.App(_, as) => as.flatMap(collectVarSpans(_, vs))
    case Term.As(x, _) => collectVarSpans(x, vs)
    case Term.Ascr(x, _) => collectVarSpans(x, vs)
    case p @ Term.Proj(v, _) => collectVarSpans(v, vs)
    case Term.With(v, fs) => collectVarSpans(v, vs) ++ fs.flatMap(f => collectVarSpans(f._2, vs))
    case Term.Arith(_, l, r) => collectVarSpans(l, vs) ++ collectVarSpans(r, vs)
    case Term.Neg(x) => collectVarSpans(x, vs)
    case _ => Nil
