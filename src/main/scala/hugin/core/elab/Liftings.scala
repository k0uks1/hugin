package hugin.core
package elab

import hugin.obj.BaseType
import hugin.syntax.Tree
import hugin.syntax.Trees.*
import hugin.util.*

/** The lifting judgement of shared data (reference: meta/staging, the rule Lift):
 *
 *  {{{
 *    Δ ⊢ b ⇝ persist_b  (b base)     Δ ⊢ a ⇝ f  ((a ↦ f) ∈ Δ)     Δ ⊢ ⇑A ⇝ [x] x
 *    Δ ⊢ T τ̄ ⇝ T.lift ē   (T shared, Δ ⊢ τᵢ ⇝ eᵢ)
 *  }}}
 *
 *  with the object type `b⁰ = b`, `(⇑A)⁰ = A`, `(T τ̄)⁰ = T τ̄⁰`. Stage inference uses it with Δ empty: a meta
 *  value `e : τ` used as object code of type `τ⁰` is `$(ℓ e)` ([[liftCode]]); for a base type that is the
 *  persisted literal and for `⇑A` the splice, the conversions stage inference had before. The reflective
 *  counterpart `⇝ʳ` (`tint`/`tfloat`/`tstr`, `T.reify`, no rule for `⇑A`) turns a meta value into `term`
 *  data, for a hole of a quote ([[reifyCode]]). The judgement is syntax-directed: a lifting is unique. */
trait Liftings:
  self: Elaborator =>
  import core.*

  /** The rule Lift: the meta code `t : a` as object code, with its object type, if `a` has a lifting. */
  def liftCode(c: Cxt, t: Tm, a: Val): Option[(Tm, Val)] = forceData(a) match
    case Val.Lift(x) => Some((Tm.splice(t), x))
    case Val.Base(b, Stage.S1) => Some((Tm.Persist(t), Val.Base(b, Stage.S0)))
    case other => sharedLifting(c, other).map((l, o) => (Tm.Splice(Tm.App(l, t, Icit.Expl)), o))

  /** `· ⊢ a ⇝ ℓ`: `ℓ : a → ⇑a⁰` as a meta function, and `a⁰`. */
  private def lifting(c: Cxt, a: Val): Option[(Tm, Val)] = forceData(a) match
    case Val.Lift(x) => Some((Tm.Lam("x", Icit.Expl, Tm.Var(0)), x))
    case Val.Base(b, Stage.S1) => Some((Tm.Lam("x", Icit.Expl, Tm.Quote(Tm.Persist(Tm.Var(0)))), Val.Base(b, Stage.S0)))
    case other => sharedLifting(c, other)

  private def sharedLifting(c: Cxt, a: Val): Option[(Tm, Val)] = sharedApplication(a).filter(_._1.lift >= 0).flatMap {
    (link, args) =>
      val parts = args.map(lifting(c, _))
      Option.when(parts.forall(_.isDefined)) {
        val elems = args.zip(parts.flatten).map { case (arg, (l, o)) =>
          (l, Val.Pi("x", Icit.Expl, arg, closureOf(c, Tm.Lift(quote(c.lvl + 1, o)))))
        }
        derived(c, link.lift, elems, a)
      }.flatten.flatMap { (t, res) =>
        forceData(res) match
          case Val.Lift(o) => Some((t, o))
          case _ => None
      }
  }

  /** The reflective counterpart: the meta value `t : a` as `term` data, if `a` has a reification. */
  def reifyCode(c: Cxt, t: Tm, a: Val): Option[Tm] = reifying(c, a).map {
    case Tm.Lam(_, _, Tm.App(f, Tm.Var(0), i)) => Tm.App(f, t, i)
    case r => Tm.App(r, t, Icit.Expl)
  }

  /** `· ⊢ a ⇝ʳ r`: `r : a → term`. */
  private def reifying(c: Cxt, a: Val): Option[Tm] = reflectiveGlobals.flatMap { r =>
    forceData(a) match
      case Val.Base(b, Stage.S1) =>
        val ctor = b match
          case BaseType.IntT => "tint"
          case BaseType.FloatT => "tfloat"
          case BaseType.StringT => "tstr"
        Some(Tm.Lam("x", Icit.Expl, Tm.App(Tm.Global(r.ctor(ctor)), Tm.Var(0), Icit.Expl)))
      case other =>
        sharedApplication(other).filter(_._1.reify >= 0).flatMap { (link, args) =>
          val parts = args.map(reifying(c, _))
          Option.when(parts.forall(_.isDefined)) {
            val elems = args.zip(parts.flatten).map((arg, f) => (f, Val.Pi("x", Icit.Expl, arg, closureOf(c, Tm.Global(r.term)))))
            derived(c, link.reify, elems, other).map(_._1)
          }.flatten
        }
  }

  /** A shared meta family applied to its arguments. */
  private def sharedApplication(a: Val): Option[(SharedLink, List[Val])] = a match
    case Val.Rigid(Head.Glob(id), sp) if sp.forall(_.isInstanceOf[Elim.EApp]) =>
      sharedFamily(id).map(l => (l, sp.reverse.collect { case Elim.EApp(x, _) => x }))
    case _ => None

  /** `fn ē` for a derived function `fn : {…} → (a₁ → …) → … → T ā → R` applied to the element functions
   *  `ē` (with their types): the application and `R`, its implicit arguments solved by unification with the
   *  types of `ē` and with `a`. */
  private def derived(c: Cxt, fn: Int, elems: List[(Tm, Val)], a: Val): Option[(Tm, Val)] =
    def explicitPi(ty: Val): (Val, Closure) = force(ty) match
      case Val.Pi(_, Icit.Expl, dom, cl) => (dom, cl)
      case _ => throw UnifyError(UnifyFailure.Mismatch)
    try
      undoOnFailure {
        var (t, ty, _) = insertAll(c, Span.NoSpan, (Tm.Global(fn), globals(fn).ty, Stage.S1))
        for (f, fty) <- elems do
          val (dom, cl) = explicitPi(ty)
          unify(c.lvl, fty, dom)
          t = Tm.App(t, f, Icit.Expl)
          ty = inst(cl, ev(c, f))
        val (dom, cl) = explicitPi(ty)
        unify(c.lvl, a, dom)
        Some((t, inst(cl, Val.Wild)))
      }
    catch case _: UnifyError => None

  private def closureOf(c: Cxt, body: Tm): Closure = Closure(c.env, body)

  /** The first type in `a` that is not shared, if `a` has no lifting (for the note of E0902). */
  def firstUnshared(c: Cxt, a: Val): Option[String] = forceData(a) match
    case Val.Lift(_) | Val.Base(_, Stage.S1) => None
    case other =>
      sharedApplication(other) match
        case Some((_, args)) => args.iterator.flatMap(firstUnshared(c, _)).nextOption()
        case None => Some(show(c, other))

  /** List syntax at the object stage: `[ē]` and `e :: es` are applications of the object constructors of
   *  the prelude's `list`. */
  def objectList(t: Tree): Tree =
    val r = reflective(t.span)
    def nil = SymRef(sharedAt(r.nil, Stage.S0), "nil")(t.span)
    def cons(h: Tree, tl: Tree) = Apply(Apply(SymRef(sharedAt(r.cons, Stage.S0), "cons")(t.span), h)(h.span), tl)(h.span.to(t.span))
    t match
      case ListLit(es) => es.foldRight(nil: Tree)(cons)
      case ConsE(h, tl) => cons(h, tl)
      case other => other
