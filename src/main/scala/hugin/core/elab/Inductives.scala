package hugin.core
package elab

import hugin.syntax.Literal
import hugin.syntax.Trees.*
import hugin.util.*

/** Inductive families (reference: meta/families). A meta declaration without clauses is classified by its
 *  type: `T : Δ -> Type.` declares an inductive family, `c : Δ -> T ū.` (for a family `T` of the module)
 *  one of its constructors; anything else is a postulate. Constructors are checked for strict positivity
 *  and predicativity (their arguments live in the family's universe). All arguments of a family are
 *  treated as indices: pattern matching unifies them (no separate parameters are needed).
 *
 *  Nat literals (Q2): a family with exactly a constant constructor and a constructor with one recursive
 *  argument (`zero : nat.  suc : nat -> nat.`) is *nat-like*; a literal `n` checked against it is
 *  `suc (… (suc zero))`, also in patterns. */
trait Inductives:
  self: Elaborator =>
  import core.*

  /** The kind of a meta-level declaration without definition. */
  def classifyMetaConstant(d: Decl, ty: Val): GlobalKind =
    if state.functionNames(d.name.name) then GlobalKind.Function(-1, None)
    else
      val (binders, result) = telescope(ty)
      force(result) match
        case Val.U1(_) => GlobalKind.Inductive(Nil)
        case Val.Rigid(Head.Glob(fam), sp) if isFamily(fam) && scope.get(globals(fam).name).contains(fam) =>
          checkConstructor(d, fam, binders, sp)
          GlobalKind.Constructor(fam)
        case Val.Base(b, _) if binders.isEmpty =>
          fail(ElabProblem.Unclassifiable(d.name.name, b.show, true, d.tpe.span))
        case Val.U0 | Val.Lift(Val.U0) => fail(ElabProblem.TypeFunction(d.name.name, d.tpe.span))
        case _ => GlobalKind.Postulate

  def isFamily(id: Int): Boolean = globals(id).kind.isInstanceOf[GlobalKind.Inductive]
  def isConstructor(id: Int): Boolean = globals(id).kind.isInstanceOf[GlobalKind.Constructor]

  def constructors(fam: Int): List[Int] = globals(fam).kind match
    case GlobalKind.Inductive(cs) => cs
    case _ => Nil

  /** Registers a declared constructor with its family. */
  def addConstructor(fam: Int, ctor: Int): Unit =
    globals(fam).kind = GlobalKind.Inductive(constructors(fam) :+ ctor)

  /** The Π binders of a closed type (name, icit, type, as values over the binders before) and its
   *  result, instantiated with variables at levels 0, 1, …. */
  def telescope(ty: Val): (List[(Name, Icit, Val)], Val) =
    def go(t: Val, l: Int, acc: List[(Name, Icit, Val)]): (List[(Name, Icit, Val)], Val) = force(t) match
      case Val.Pi(x, i, a, cl) => go(inst(cl, Val.local(l)), l + 1, (x, i, a) :: acc)
      case other => (acc.reverse, other)
    go(ty, 0, Nil)

  /** Constructor `c : Δ -> T ū`: `T` fully applied, `T` only strictly positive in Δ, Δ in T's universe. */
  private def checkConstructor(d: Decl, fam: Int, binders: List[(Name, Icit, Val)], resultSp: Spine): Unit =
    val famTy = telescope(globals(fam).ty)
    if resultSp.length != famTy._1.length then
      fail(ClauseProblem.PartialFamilyResult(globals(fam).name, d.tpe.span))
    binders.zipWithIndex.foreach { case ((x, _, a), l) =>
      if !strictlyPositive(fam, l, a) then
        fail(ClauseProblem.NonPositive(globals(fam).name, l + 1, showVal(binders.take(l).map(_._1).reverse, a), d.tpe.span))
    }
    val famLevel = force(famTy._2) match
      case Val.U1(k) => k
      case _ => Level.zero
    val types = binders.map(_._3).toVector
    val forced = forcedBinders(binders, resultSp)
    binders.zipWithIndex.filterNot((_, l) => forced(l)).foreach { case ((x, _, a), l) =>
      typeLevels(types.take(l), l, a).foreach { k =>
        if !levels.le(k, famLevel) then
          fail(ClauseProblem.ArgumentTooLarge(x, globals(fam).name, showLevel(famLevel), d.tpe.span))
      }
    }

  /** The implicit binders of a constructor that are arguments of its result (`A` in `scons : A -> seq A ->
   *  seq A`): forced by the type, like parameters, so they do not count for predicativity (otherwise a
   *  family over `Type` could not hold its elements in its own universe, and nested families such as
   *  `tapp : sym -> seq term -> term` would be universe-inconsistent). */
  private def forcedBinders(binders: List[(Name, Icit, Val)], resultSp: Spine): Set[Int] =
    val args = resultSp.collect { case Elim.EApp(Val.Rigid(Head.Local(x), Nil), _) => x }.toSet
    binders.zipWithIndex.collect { case ((_, Icit.Impl, _), l) if args(l) => l }.toSet

  /** `T` occurs strictly positively in `a` (over `l` variables): `a` does not mention `T`, or is
   *  `(ȳ : B̄) -> T w̄` with `T` neither in `B̄` nor in `w̄`, or `T` occurs strictly positively in an argument
   *  of another family that is positive in that argument (nested, `seq term`). */
  private def strictlyPositive(fam: Int, l: Int, a: Val): Boolean =
    force(a) match
      case Val.Pi(_, _, b, cl) => !mentions(fam, l, b) && strictlyPositive(fam, l + 1, inst(cl, Val.local(l)))
      case Val.Rigid(Head.Glob(f), sp) if f == fam =>
        sp.forall {
          case Elim.EApp(x, _) => !mentions(fam, l, x)
          case _ => false
        }
      case Val.Rigid(Head.Glob(f), sp) if isFamily(f) =>
        sp.reverse.zipWithIndex.forall {
          case (Elim.EApp(x, _), j) => !mentions(fam, l, x) || positiveIn(f, j) && strictlyPositive(fam, l, x)
          case _ => false
        }
      case other => !mentions(fam, l, other)

  /** Whether family `f` is strictly positive in its argument `j`: every constructor takes it as a forced
   *  binder, which its arguments use only strictly positively (as `A` or in `f … A …` at `j`). */
  private def positiveIn(f: Int, j: Int): Boolean =
    constructors(f).nonEmpty && constructors(f).forall { c =>
      val (binders, result) = telescope(globals(c).ty)
      force(result) match
        case Val.Rigid(_, rsp) =>
          rsp.reverse.lift(j) match
            case Some(Elim.EApp(Val.Rigid(Head.Local(v), Nil), _)) =>
              binders.zipWithIndex.forall { case ((_, _, b), k) => k <= v || onlyPositive(f, j, v, k, b) }
            case _ => false
        case _ => false
    }

  /** The variable `v` occurs in `b` (over `k` variables) only strictly positively for argument `j` of `f`. */
  private def onlyPositive(f: Int, j: Int, v: Int, k: Int, b: Val): Boolean = force(b) match
    case Val.Rigid(Head.Local(x), Nil) if x == v => true
    case Val.Pi(_, _, d, cl) => !occurs(k - v - 1, quote(k, d)) && onlyPositive(f, j, v, k + 1, inst(cl, Val.local(k)))
    case Val.Rigid(Head.Glob(g), sp) if g == f =>
      sp.reverse.zipWithIndex.forall {
        case (Elim.EApp(x, _), i) => if i == j then onlyPositive(f, j, v, k, x) else !occurs(k - v - 1, quote(k, x))
        case _ => false
      }
    case other => !occurs(k - v - 1, quote(k, other))

  private def mentions(fam: Int, l: Int, v: Val): Boolean = mentionsTm(fam, quote(l, v))

  private def mentionsTm(fam: Int, t: Tm): Boolean = Tm.exists(t) {
    case Tm.Global(g) => g == fam
    case _ => false
  }

  // ---------------------------------------------------------------- nat literals

  /** For a nat-like family: its zero and successor constructors. */
  def natLike(fam: Int): Option[(Int, Int)] =
    def shape(c: Int): Option[Boolean] = telescope(globals(c).ty) match
      case (Nil, _) => Some(false)
      case (List((_, Icit.Expl, a)), _) if isFam(a, fam) => Some(true)
      case _ => None
    val tyArgs = telescope(globals(fam).ty)._1
    constructors(fam) match
      case List(a, b) if tyArgs.isEmpty =>
        (shape(a), shape(b)) match
          case (Some(false), Some(true)) => Some((a, b))
          case (Some(true), Some(false)) => Some((b, a))
          case _ => None
      case _ => None

  private def isFam(a: Val, fam: Int): Boolean = force(a) match
    case Val.Rigid(Head.Glob(f), Nil) => f == fam
    case _ => false

  /** The nat-like family a type is, with its constructors. */
  def natType(ty: Val): Option[(Int, Int)] = force(ty) match
    case Val.Rigid(Head.Glob(f), Nil) if isFamily(f) => natLike(f)
    case _ => None

  /** `n` as `suc (… zero)`. */
  def natTerm(zero: Int, suc: Int, n: Long): Tm =
    (1L to n).foldLeft(Tm.Global(zero): Tm)((acc, _) => Tm.App(Tm.Global(suc), acc, Icit.Expl))

  /** A literal checked against a nat-like type. */
  def natLiteral(c: Cxt, l: Literal, ty: Val, span: Span): Option[Tm] = (l, natType(ty)) match
    case (Literal.IntL(n), Some((z, s))) =>
      if n < 0 then fail(TypeProblem.NegativeNat(show(c, ty), span))
      if n > 100000 then fail(TypeProblem.NatTooLarge(span))
      Some(natTerm(z, s, n))
    case _ => None
