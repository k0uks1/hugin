package hugin.obj
package typing

import hugin.util.*
import hugin.compiler.*
import scala.collection.mutable

/** Binding steps, canonical order and range restriction (Section 6.3). Relations have no modes (reference:
 *  object/rules): an atom binds all its variables. */
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

  /** Why a formula cannot take a binding step. */
  enum Stuck:
    case Unbound(f: Formula, missing: Set[String])
    case Inner(f: Formula, inner: Stuck)

  /** B ⊢ φ ⇒ B' (Definition 6.3). */
  def step(f: Formula, b: Set[String]): Either[Stuck, Set[String]] = f match
    case Formula.Atom(_, args, _) =>
      // arithmetic, projections and updates in an argument are computed, not matched
      val missing = args.flatMap(needs).toSet -- b
      if missing.isEmpty then Right(b ++ formulaVars(f)) else Left(Stuck.Unbound(f, missing))
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
    case Formula.Not(Formula.Atom(_, args, _)) =>
      if !args.forall(x => needs(x).subsetOf(b)) then Left(Stuck.Unbound(f, args.flatMap(needs).toSet -- b))
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

  /** Greedy canonical order (Lemma 6.4): repeatedly pick the leftmost formula that can step. */
  def canonical(body: List[Formula], b0: Set[String]): Either[Stuck, (List[Formula], Set[String])] =
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

  def describe(s: Stuck): Diagnostic = problem(s).toDiagnostic

  /** Why the canonical order got stuck. */
  def problem(s: Stuck): ModingError = s match
    case Stuck.Unbound(f, missing) =>
      val site = f match
        case Formula.Cmp(CmpOp.Eq, _, _) => UnboundSite.Equation
        case Formula.Cmp(_, _, _) => UnboundSite.Comparison
        case Formula.Agg(_, _, _, _) => UnboundSite.Aggregate
        case Formula.Not(_) => UnboundSite.Negation
        case _ => UnboundSite.Other
      ModingError.UnboundInFormula(missing.toList.sorted.map(VarName(_)), site, f.span)
    case Stuck.Inner(_, inner) => problem(inner)

/** Phase: range restriction of every rule and query (Definitions 6.3–6.5). */
final class ModingPhase extends Phase:
  def phaseName = "moding"
  def description = "check range restriction"
  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    p.rules = p.rules.filter { r =>
      Moding.canonical(r.body, Set.empty) match
        case Left(stuck) =>
          ctx.report(Diag.rule(r)(Moding.describe(stuck)))
          false
        case Right((_, b)) =>
          val missing = r.heads.flatMap(Moding.vars).toSet -- b
          if missing.nonEmpty then
            val spans = r.heads.flatMap(collectVarSpans(_, missing))
            val vs = missing.toList.sorted.map(VarName(_))
            ctx.report(Diag.rule(r)(ModingError.NotRangeRestricted(vs, spans.headOption.getOrElse(r.span), spans.drop(1)).toDiagnostic))
          missing.isEmpty
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
