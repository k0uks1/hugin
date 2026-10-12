package hugin.core
package elab

import hugin.syntax.{Literal, Tree}
import hugin.syntax.Trees.*
import hugin.util.*

/** Inductive families (reference: meta/families). A meta declaration without clauses is classified by its
 *  type: `T : Δ -> Type.` declares an inductive family, `c : Δ -> T ū.` (for a family `T` of the module)
 *  one of its constructors; anything else is a function defined by no clauses ([[Items.checkClauseless]]).
 *  Constructors are checked for strict positivity and predicativity (their arguments live in the family's
 *  universe). Pattern matching unifies all arguments of a family, but its leading arguments that every
 *  constructor keeps fixed are its *parameters* (D2 of the proofs note; Lean's `autoPromoteIndices`): a
 *  constructor's implicit binders at their positions are exempt from predicativity, and they are not
 *  subterms of the constructor's applications for termination.
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
        // the meta `int` of another file: as the base type it is written as
        case i if binders.isEmpty && isMetaInt(i) => fail(ElabProblem.Unclassifiable(d.name.name, "int", true, d.tpe.span))
        case Val.U0 | Val.Lift(Val.U0) => fail(ElabProblem.TypeFunction(d.name.name, d.tpe.span))
        // a function without clauses: its coverage is checked once the file's constructors are declared
        case _ if state.clauseless(d.name.name) => GlobalKind.Function(-1, None)
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
   *  result, instantiated with variables at levels `from`, `from + 1`, …. */
  def telescope(ty: Val, from: Int = 0): (List[(Name, Icit, Val)], Val) =
    def go(t: Val, l: Int, acc: List[(Name, Icit, Val)]): (List[(Name, Icit, Val)], Val) = force(t) match
      case Val.Pi(x, i, a, cl) => go(inst(cl, Val.local(l)), l + 1, (x, i, a) :: acc)
      case other => (acc.reverse, other)
    go(ty, from, Nil)

  /** Constructor `c : Δ -> T ū`: `T` fully applied, `T` only strictly positive in Δ, Δ in T's universe. */
  private def checkConstructor(d: Decl, fam: Int, binders: List[(Name, Icit, Val)], resultSp: Spine): Unit =
    val famTy = telescope(globals(fam).ty)
    if resultSp.length != famTy._1.length then
      fail(ClauseProblem.PartialFamilyResult(globals(fam).name, d.tpe.span))
    binders.zipWithIndex.foreach { case ((x, _, a), l) =>
      if !strictlyPositive(Set(fam), l, a) then
        fail(ClauseProblem.NonPositive(globals(fam).name, l + 1, showVal(binders.take(l).map(_._1).reverse, a), d.tpe.span))
    }
    mutualViolation(fam, binders).foreach { (c, l, before, a, block) =>
      val shown = block.find(g => familiesIn(l, a).contains(g)).getOrElse(fam)
      fail(
        ClauseProblem.NonPositive(
          globals(shown).name,
          l + 1,
          showVal(before.map(_._1).reverse, a),
          d.tpe.span,
          block.filter(_ != shown).map(g => globals(g).name).toList,
          c.map(globals(_).name)
        )
      )
    }
    val famLevel = force(famTy._2) match
      case Val.U1(k) => k
      case _ => Level.zero
    // D2 (Lean's `autoPromoteIndices`): the leading arguments that every constructor keeps fixed are the
    // family's parameters; only implicit binders at parameter positions are exempt from predicativity
    val before = parameters(fam)
    val promoted = before.min(fixedPrefix(fam, binders, resultSp))
    if promoted < before then
      // this constructor turns arguments of the family into indices: the constructors declared before it
      // lose the exemption of their binders at those positions
      for c <- constructors(fam) do
        val (cb, cr) = telescope(globals(c).ty)
        val csp = force(cr) match
          case Val.Rigid(_, sp) => sp
          case _ => Nil
        checkLevels(fam, famLevel, cb, csp, parameterBinders(cb, csp, promoted), d, Some(globals(c).name))
    checkLevels(fam, famLevel, binders, resultSp, parameterBinders(binders, resultSp, promoted), d, None)
    globals(fam).parameters = promoted

  /** The binders of a constructor `binders -> fam resultSp` outside `exempt` live in the family's
   *  universe `famLevel`; `other` names the constructor if it is not the one declared by `d`. A forced
   *  implicit binder that is not exempt is an index of the family, which the error says. */
  private def checkLevels(
      fam: Int,
      famLevel: Level,
      binders: List[(Name, Icit, Val)],
      resultSp: Spine,
      exempt: Set[Int],
      d: Decl,
      other: Option[Name]
  ): Unit =
    val types = binders.map(_._3).toVector
    val forced = forcedBinders(binders, resultSp)
    binders.zipWithIndex.filterNot((_, l) => exempt(l)).foreach { case ((x, _, a), l) =>
      typeLevels(types.take(l), l, a).foreach { k =>
        if !levels.le(k, famLevel) then
          fail(ClauseProblem.ArgumentTooLarge(x, globals(fam).name, showLevel(famLevel), d.tpe.span, other, forced(l)))
      }
    }

  /** The implicit binders of a constructor that are arguments of its result (`A` in `cons : A -> list A ->
   *  list A`): forced by the type. Those at the family's parameter positions do not count for
   *  predicativity (otherwise a family over `Type` could not hold its elements in its own universe, and
   *  nested families such as `tapp : sym -> list term -> term` would be universe-inconsistent); those at
   *  its indices do (D2, Agda's default `--no-large-indices`). */
  private def forcedBinders(binders: List[(Name, Icit, Val)], resultSp: Spine): Set[Int] =
    val args = resultSp.collect { case Elim.EApp(Val.Rigid(Head.Local(x), Nil), _) => x }.toSet
    binders.zipWithIndex.collect { case ((_, Icit.Impl, _), l) if args(l) => l }.toSet

  /** The number of parameters of the family `fam` (reference: meta/families, "Parameters"): its leading
   *  arguments that every constructor declared so far keeps fixed; all its arguments while it has none. */
  def parameters(fam: Int): Int =
    val g = globals(fam)
    if g.parameters >= 0 then g.parameters else telescope(g.ty)._1.length

  /** The implicit binders of a constructor (with the result spine `resultSp`) that are the variables at
   *  the family's first `params` positions: its parameters, exempt from predicativity. */
  private def parameterBinders(binders: List[(Name, Icit, Val)], resultSp: Spine, params: Int): Set[Int] =
    val forced = forcedBinders(binders, resultSp)
    resultArgs(resultSp).take(params).flatMap(localOf).filter(forced).toSet

  /** The binders of the constructor `ctor` at its family's parameter positions: not subterms of the
   *  constructor's applications for termination, as parameters are not arguments of a constructor in Lean
   *  or Agda (reference: meta/termination). */
  def parameterArguments(ctor: Int): Set[Int] = globals(ctor).kind match
    case GlobalKind.Constructor(fam) =>
      force(telescope(globals(ctor).ty)._2) match
        case Val.Rigid(_, sp) => resultArgs(sp).take(parameters(fam)).flatMap(localOf).toSet
        case _ => Set.empty
    case _ => Set.empty

  private def resultArgs(sp: Spine): List[Val] = sp.reverse.collect { case Elim.EApp(v, _) => v }

  private def localOf(v: Val): Option[Int] = force(v) match
    case Val.Rigid(Head.Local(x), Nil) => Some(x)
    case _ => None

  /** The number of leading arguments of `fam` that a constructor `binders -> fam resultSp` keeps fixed
   *  (Lean's `fixedIndicesToParams`): at each such position, its result has one of its binders, a
   *  different one at each position, and every occurrence of `fam` in the types of its arguments has the
   *  same binder at that position. */
  private def fixedPrefix(fam: Int, binders: List[(Name, Icit, Val)], resultSp: Spine): Int =
    val args = resultArgs(resultSp)
    var seen = Set.empty[Int]
    var p = 0
    var fixed = true
    while fixed && p < args.length do
      localOf(args(p)) match
        case Some(x) if !seen(x) && binders.zipWithIndex.forall { case ((_, _, a), l) => keepsFixed(fam, p, x, l, a) } =>
          seen += x
          p += 1
        case _ => fixed = false
    p

  /** Every occurrence of `fam` in `a` (over `l` variables) has the variable `x` at position `i`. */
  private def keepsFixed(fam: Int, i: Int, x: Int, l: Int, a: Val): Boolean = force(a) match
    case Val.Pi(_, _, b, cl) => keepsFixed(fam, i, x, l, b) && keepsFixed(fam, i, x, l + 1, inst(cl, Val.local(l)))
    case Val.Rigid(Head.Glob(f), sp) if sp.forall(_.isInstanceOf[Elim.EApp]) =>
      val as = resultArgs(sp)
      (f != fam || as.lift(i).flatMap(localOf).contains(x)) && as.forall(keepsFixed(fam, i, x, l, _))
    case other => !mentions(fam, l, other)

  /** The families `fams` (a family, or a mutual block of them) occur strictly positively in `a` (over `l`
   *  variables): `a` does not mention them, or is `(ȳ : B̄) -> T w̄` with `T` one of them and none of them
   *  in `B̄` or `w̄`, or they occur strictly positively in an argument of another family that is positive in
   *  that argument (nested, `list term`). */
  private def strictlyPositive(fams: Set[Int], l: Int, a: Val): Boolean =
    force(a) match
      case Val.Pi(_, _, b, cl) => !mentionsAny(fams, l, b) && strictlyPositive(fams, l + 1, inst(cl, Val.local(l)))
      case Val.Rigid(Head.Glob(f), sp) if fams(f) =>
        sp.forall {
          case Elim.EApp(x, _) => !mentionsAny(fams, l, x)
          case _ => false
        }
      case Val.Rigid(Head.Glob(f), sp) if isFamily(f) =>
        sp.reverse.zipWithIndex.forall {
          case (Elim.EApp(x, _), j) => !mentionsAny(fams, l, x) || positiveIn(f, j) && strictlyPositive(fams, l, x)
          case _ => false
        }
      case other => !mentionsAny(fams, l, other)

  /** Mutual families (#186 P5): families whose constructors refer to each other, directly or through
   *  other families, form a *mutual block*, a strongly connected component of the graph "a constructor of
   *  `F` mentions `G` in an argument type". Every family of a block must occur strictly positively in the
   *  constructors of every family of the block, as in Agda (`Agda.TypeChecking.Positivity`, over the
   *  occurrence graph of a mutual block), Lean 4 (the kernel's positivity check over all types of a
   *  `mutual` block) and Coq. The check of a constructor against its own family alone would accept
   *  `a : Type. b : Type. mkA : (b -> empty) -> a. mkB : a -> b.`, whose `loop (mkB (mkA f)) = f (mkB (mkA
   *  f))` proves `empty`. Families need no `mutual` keyword: the block of a constructor's family is
   *  recomputed when the constructor is declared (`binders`, not yet registered), and if it has other
   *  members, every constructor of the block is checked against all of them. A constructor that closes a
   *  cycle is so checked before any function can use it. `None`, or the first argument that is not
   *  strictly positive: its constructor (`None` for the one declared), its index, its binders before it
   *  and its type, and the block. */
  private def mutualViolation(
      fam: Int,
      binders: List[(Name, Icit, Val)]
  ): Option[(Option[Int], Int, List[(Name, Icit, Val)], Val, Vector[Int])] =
    val known = scala.collection.mutable.Map.empty[Int, Set[Int]]
    def mentioned(bs: List[(Name, Icit, Val)]): Set[Int] =
      bs.zipWithIndex.flatMap { case ((_, _, a), l) => familiesIn(l, a) }.toSet
    def edges(f: Int): Set[Int] =
      known.getOrElseUpdate(
        f,
        constructors(f).flatMap(c => mentioned(telescope(globals(c).ty)._1)).toSet ++ (if f == fam then mentioned(binders) else Set.empty)
      )
    // the families from which `fam` is reachable, among those reachable from it
    val reach = scala.collection.mutable.LinkedHashSet.empty[Int]
    def forward(f: Int): Unit = if reach.add(f) then edges(f).foreach(forward)
    forward(fam)
    // those of them from which `fam` is reachable (a fixpoint over the reachable families)
    var onCycle = Set(fam)
    var grown = true
    while grown do
      val more = reach.filter(f => !onCycle(f) && edges(f).exists(onCycle))
      grown = more.nonEmpty
      onCycle ++= more
    val block = reach.toVector.filter(onCycle)
    if block.length < 2 then None
    else
      val members = block.toSet
      val ctors = block.flatMap(f => constructors(f).map(c => (Option(c), telescope(globals(c).ty)._1))) :+ (None, binders)
      ctors.iterator.flatMap { (c, bs) =>
        bs.zipWithIndex.find { case ((_, _, a), l) => !strictlyPositive(members, l, a) }.map { case ((_, _, a), l) =>
          (c, l, bs.take(l), a, block)
        }
      }.nextOption()

  /** The inductive families that `a` (over `l` variables) mentions. */
  private def familiesIn(l: Int, a: Val): Set[Int] =
    var out = Set.empty[Int]
    Tm.exists(quote(l, a)) {
      case Tm.Global(g) if isFamily(g) => out += g; false
      case _ => false
    }
    out

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

  private def mentions(fam: Int, l: Int, v: Val): Boolean = mentionsAny(Set(fam), l, v)

  private def mentionsAny(fams: Set[Int], l: Int, v: Val): Boolean = Tm.exists(quote(l, v)) {
    case Tm.Global(g) => fams(g)
    case _ => false
  }

  // ---------------------------------------------------------------- nat literals

  /** A literal checked against a nat-like type. */
  def natLiteral(c: Cxt, l: Literal, ty: Val, span: Span): Option[Tm] = (l, natType(ty)) match
    case (Literal.IntL(n), Some((z, s))) =>
      if n < 0 then fail(TypeProblem.NegativeNat(show(c, ty), span))
      Some(natTerm(z, s, n))
    case _ => None

  /** `e + k` checked against the nat-like family with the successor `suc`: `suc` applied `k` times. */
  def natSuccessor(suc: Int, e: Tm, k: Long, span: Span): Tm = natSucc(suc, e, k)

  /** `k` if `t` is an integer literal of at least 1: the right operand of `e + k` on a nat-like type
   *  (reference: meta/families, numerals). */
  def successorCount(t: Tree): Option[Long] = t match
    case Parens(i) => successorCount(i)
    case Lit(Literal.IntL(k)) if k >= 1 => Some(k)
    case _ => None
