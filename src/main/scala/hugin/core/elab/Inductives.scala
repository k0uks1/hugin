package hugin.core
package elab

import hugin.syntax.Literal
import hugin.syntax.Trees.*
import hugin.util.*
import hugin.util.diagnostics.{Code as DiagCode, Legacy}

/** Inductive families (REDESIGN §6.2–6.3). A meta declaration without clauses is classified by its
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
        case Val.Rigid(Head.Glob(fam), sp) if isFamily(fam) =>
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
      fail(
        Legacy.error(
          DiagCode.E0914,
          s"a constructor of `${globals(fam).name}` must return it applied to all its arguments",
          d.tpe.span,
          "partially applied family"
        )
      )
    binders.zipWithIndex.foreach { case ((x, _, a), l) =>
      if !strictlyPositive(fam, l, a) then
        fail(
          Legacy.error(
            DiagCode.E0913,
            s"`${globals(fam).name}` occurs in a non-positive position",
            d.tpe.span,
            s"in the type of the constructor's argument ${l + 1}"
          )
            .withNote(s"the argument has type `${showVal(binders.take(l).map(_._1).reverse, a)}`")
            .withNote(
              "a family may only occur strictly positively in the arguments of its constructors: not to the left of an arrow, nor inside the arguments of another type"
            )
        )
    }
    val famLevel = force(famTy._2) match
      case Val.U1(k) => k
      case _ => Level.zero
    val types = binders.map(_._3).toVector
    binders.zipWithIndex.foreach { case ((x, _, a), l) =>
      typeLevels(types.take(l), l, a).foreach { k =>
        if !levels.le(k, famLevel) then
          fail(
            Legacy.error(
              DiagCode.E0914,
              s"the argument `$x` is too large for `${globals(fam).name}`",
              d.tpe.span,
              "argument in a larger universe"
            )
              .withNote(
                s"`${globals(fam).name}` lives in `${showLevel(famLevel)}`; its constructors may only take arguments of types in that universe (predicativity)"
              )
          )
      }
    }

  /** `T` occurs strictly positively in `a` (over `l` variables): `a` does not mention `T`, or is
   *  `(ȳ : B̄) -> T w̄` with `T` neither in `B̄` nor in `w̄`. */
  private def strictlyPositive(fam: Int, l: Int, a: Val): Boolean =
    force(a) match
      case Val.Pi(_, _, b, cl) => !mentions(fam, l, b) && strictlyPositive(fam, l + 1, inst(cl, Val.local(l)))
      case Val.Rigid(Head.Glob(f), sp) if f == fam =>
        sp.forall {
          case Elim.EApp(x, _) => !mentions(fam, l, x)
          case _ => false
        }
      case other => !mentions(fam, l, other)

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
      if n < 0 then error(DiagCode.E0901, "mismatched types", span, s"a negative number is not a `${show(c, ty)}`")
      if n > 100000 then error(DiagCode.E0901, "nat literal too large", span, "at most 100000 (nats are unary)")
      Some(natTerm(z, s, n))
    case _ => None
