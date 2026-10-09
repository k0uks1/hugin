package hugin.core
package elab

import hugin.obj.BaseType
import hugin.syntax.Tree
import hugin.syntax.Trees.*
import hugin.util.*
import scala.collection.mutable

/** The functions derived from shared data declarations ([[SharedData]]): for each shared family `T ā` of
 *  the file,
 *
 *  {{{
 *    T.lift  : (a₁ → ⇑b₁) → … → T ā → ⇑(T b̄)      T.lift f̄ (cᵢ x̄) = cᵢ (L[σ₁] x₁) …
 *    T.reify : (a₁ → term) → … → T ā → term         T.reify ḡ (cᵢ x̄) = '{ cᵢ $(R[σ₁] x₁) … }
 *  }}}
 *
 *  generated as surface clauses and elaborated like hand-written ones, so coverage and size-change
 *  termination are checked. An argument of a parameter's type is converted by its element function, one
 *  of a closed type by stage inference itself (the rule Lift, or a hole of a reflected type), one of a
 *  shared type of the file by a direct call of that type's function. A *nested* occurrence of the file's
 *  types (`option shape` in a constructor of `shape`, `list (tree A)` in one of `tree A`) is converted by
 *  a helper `T.lift.k`, the fold of the outer type specialised at its arguments, with direct recursive
 *  calls (as `openTs` is written next to `openT` in the prelude): passing `T.lift` to `option.lift` would
 *  be a call that size-change termination cannot see through. */
trait DerivedFunctions:
  self: Elaborator =>
  import core.*

  /** A shareable type over the parameters of the family being derived (validated by [[SharedData]]). */
  private enum Ty:
    case Param(index: Int)
    case Base(b: BaseType)
    case App(family: Int, args: List[Ty])

  /** The derivation of one function (`lift` or `reify`) for the families of the file: the helpers made
   *  so far, by owner family and nested type, and the clauses still to elaborate. */
  private final class Derivation(val lift: Boolean, val group: Set[Int]):
    val helpers = mutable.LinkedHashMap.empty[(Int, Ty), Int]
    val clauses = mutable.ListBuffer.empty[(Int, List[SurfaceClause])]

  /** Declares `T.lift` (or `T.reify`) of the shared family `m`. */
  def declareShared(m: Int, lift: Boolean): Int =
    val n = telescope(globals(m).ty)._1.length
    val self = Ty.App(m, (0 until n).map(Ty.Param(_)).toList)
    declareFunction(s"${globals(m).name}.${if lift then "lift" else "reify"}", m, n, self, lift)

  /** The clauses of `T.lift` and `T.reify` for the shared types of the file, now that their constructors
   *  are declared. `T.reify` is declared here if it is not yet: its type needs `term`, which may be
   *  declared after `T` (the prelude's `list` comes before the reflective types, whose sequences are
   *  lists). */
  def defineSharedFunctions(): Unit =
    val fams = state.sharedDeclared.filter(fam => scope.get(globals(fam).name).contains(fam))
    if reflectiveGlobals.isDefined then
      for fam <- fams if globals(fam).shared.get.reify < 0 do
        try globals(fam).shared.get.reify = declareShared(fam, lift = false)
        catch case e: ElabError => report(e)
    for lift <- List(true, false) do
      val dv = Derivation(lift, fams.toSet)
      for fam <- fams do
        val link = globals(fam).shared.get
        val fn = if lift then link.lift else link.reify
        val n = telescope(globals(fam).ty)._1.length
        if fn >= 0 then dv.clauses += fn -> clausesFor(dv, fam, fn, fam, (0 until n).map(Ty.Param(_)).toList)
      dv.clauses.foreach(defineDerived)

  private def defineDerived(fn: Int, clauses: List[SurfaceClause]): Unit =
    val start = metas.length
    try
      undoOnFailure {
        if clauses.nonEmpty then elabFunction(fn, clauses)
        checkSolved(start)
      }
    catch case e: ElabError => report(e)

  /** Declares a derived function `name : (A₁ → E₁) → … → (Aₙ → Eₙ) → τ[Ā] → R[B̄]` with the element functions
   *  of the family `owner`'s `n` parameters, for values of type `self`. */
  private def declareFunction(name: String, owner: Int, n: Int, self: Ty, lift: Boolean): Int =
    val g = globals(owner)
    val sp = g.declSpan
    val as = (1 to n).map(i => VarRef(s"A$i")(sp): Tree).toList
    val bs = (1 to n).map(i => VarRef(s"B$i")(sp): Tree).toList
    val term = reflectiveGlobals.map(r => SymRef(r.term, "term")(sp): Tree)
    def elem(a: Tree, b: Tree): Tree = Arrow(None, a, if lift then LiftE(b)(sp) else term.get)(sp)
    val result = if lift then LiftE(treeOf(self, bs, sp))(sp) else term.get
    val tpe = as.zip(bs).foldRight(Arrow(None, treeOf(self, as, sp), result)(sp): Tree)((ab, acc) => Arrow(None, elem(ab._1, ab._2), acc)(sp))
    state.functionNames += name
    elabDecl(Decl(Ident(name)(g.span), Nil, tpe, None, None)(sp))
    scope(name)

  /** A type as syntax, its parameters given by `params` (shared families by reference: at an object
   *  position, the object family). */
  private def treeOf(t: Ty, params: List[Tree], sp: Span): Tree = t match
    case Ty.Param(j) => params(j)
    case Ty.Base(b) => Ident(b.show)(sp)
    case Ty.App(f, args) => args.foldLeft(SymRef(f, globals(f).name)(sp): Tree)((acc, a) => Apply(acc, treeOf(a, params, sp))(sp))

  /** The explicit argument types of the meta constructor `c` of a family whose parameters are `sigma`. */
  private def argumentTys(c: Int, sigma: List[Ty]): List[Ty] =
    val (binders, result) = telescope(globals(c).ty)
    val params = forceData(result) match
      case Val.Rigid(_, sp) => sp.reverse.collect { case Elim.EApp(Val.Rigid(Head.Local(l), Nil), _) => l }
      case _ => Nil
    def ty(a: Val): Ty = forceData(a) match
      case Val.Rigid(Head.Local(x), Nil) if params.contains(x) => sigma(params.indexOf(x))
      case Val.Base(b, Stage.S1) => Ty.Base(b)
      case Val.Rigid(Head.Glob(g), sp) if sharedFamily(g).isDefined => Ty.App(g, sp.reverse.collect { case Elim.EApp(x, _) => ty(x) })
      case other => throw Impossible(s"not a shareable type: ${showVal(Nil, other)}")
    binders.collect { case (_, Icit.Expl, a) => ty(a) }

  private def mentions(t: Ty, p: Ty => Boolean): Boolean = p(t) || (t match
    case Ty.App(_, args) => args.exists(mentions(_, p))
    case _ => false
  )

  private def recursive(dv: Derivation, t: Ty): Boolean = mentions(t, {
    case Ty.App(f, _) => dv.group(f)
    case _ => false
  })

  private def closed(t: Ty): Boolean = !mentions(t, _.isInstanceOf[Ty.Param])

  /** The clauses of the function `fn` (derived for the family `owner`) on values of `family` at `sigma`:
   *  one per constructor. */
  private def clausesFor(dv: Derivation, owner: Int, fn: Int, family: Int, sigma: List[Ty]): List[SurfaceClause] =
    val n = telescope(globals(owner).ty)._1.length
    val elems = (1 to n).map(i => VarRef(s"${if dv.lift then "F" else "G"}$i")(Span.NoSpan): Tree).toList
    constructors(family).map { c =>
      val tys = argumentTys(c, sigma)
      val xs = tys.indices.map(k => VarRef(s"X${k + 1}")(Span.NoSpan): Tree).toList
      val name = globals(c).name
      val pattern = xs.foldLeft(SymRef(c, name)(Span.NoSpan): Tree)(Apply(_, _)(Span.NoSpan))
      // the object constructor: a reference to the meta one at an object position
      val converted = xs.zip(tys).map((x, t) => convert(dv, owner, elems, x, t))
      val rhs =
        if dv.lift then converted.foldLeft(SymRef(c, name)(Span.NoSpan): Tree)(Apply(_, _)(Span.NoSpan))
        else quoteOf(converted.foldLeft(SymRef(c, name)(Span.NoSpan): Tree)((acc, h) => Apply(acc, SpliceE(h)(Span.NoSpan))(Span.NoSpan)))
      SurfaceClause(Ident(globals(fn).name)(globals(owner).span), elems :+ pattern, rhs, globals(owner).declSpan)
    }

  /** The argument `x : t` converted: object code (lift; a closed type by the rule Lift) or the hole's
   *  expression (reify; a closed type by the reification of the hole). */
  private def convert(dv: Derivation, owner: Int, elems: List[Tree], x: Tree, t: Ty): Tree =
    def applied(f: Tree) = Apply(f, x)(Span.NoSpan)
    def code(f: Tree) = if dv.lift then SpliceE(applied(f))(Span.NoSpan) else applied(f)
    t match
      case Ty.Param(j) => code(elems(j))
      case Ty.App(f, args) if recursive(dv, t) && dv.group(f) && !args.exists(recursive(dv, _)) =>
        code(derivedOf(f, dv, args.map(elementFunction(dv, elems, _))))
      case Ty.App(f, args) if recursive(dv, t) =>
        val h = helper(dv, owner, t)
        code(elems.foldLeft(SymRef(h, globals(h).name)(Span.NoSpan): Tree)(Apply(_, _)(Span.NoSpan)))
      case _ if closed(t) => x
      case _ => code(elementFunction(dv, elems, t))

  /** The element function for values of `t`, a type that does not mention the file's families: a
   *  parameter's, `U.lift ē` for an open shared type, `(Y : τ) => Y` (`'{ $Y }`) for a closed one. */
  private def elementFunction(dv: Derivation, elems: List[Tree], t: Ty): Tree = t match
    case Ty.Param(j) => elems(j)
    case _ if closed(t) =>
      val y = VarRef("Y")(Span.NoSpan)
      Lambda(y, Some(treeOf(t, Nil, Span.NoSpan)), if dv.lift then y else quoteOf(SpliceE(y)(Span.NoSpan)))(Span.NoSpan)
    case Ty.App(f, args) => derivedOf(f, dv, args.map(elementFunction(dv, elems, _)))
    case Ty.Base(_) => throw Impossible("a base type is closed")

  private def derivedOf(f: Int, dv: Derivation, args: List[Tree]): Tree =
    val link = sharedFamily(f).get
    val fn = if dv.lift then link.lift else link.reify
    args.foldLeft(SymRef(fn, globals(fn).name)(Span.NoSpan): Tree)(Apply(_, _)(Span.NoSpan))

  /** The helper of `owner` for values of the nested type `t` (a shared family applied to types that
   *  mention the file's families), declared and defined once per owner and type. */
  private def helper(dv: Derivation, owner: Int, t: Ty): Int =
    dv.helpers.getOrElse(
      (owner, t), {
        val n = telescope(globals(owner).ty)._1.length
        val base = globals(if dv.lift then globals(owner).shared.get.lift else globals(owner).shared.get.reify).name
        val h = declareFunction(s"$base.${dv.helpers.count(_._1._1 == owner) + 1}", owner, n, t, dv.lift)
        dv.helpers((owner, t)) = h
        val Ty.App(f, args) = t: @unchecked
        dv.clauses += h -> clausesFor(dv, owner, h, f, args)
        h
      }
    )

  private def quoteOf(t: Tree): Tree = Quote(List(Rule(None, List(t), None)(Span.NoSpan)), terminated = false)(Span.NoSpan)
