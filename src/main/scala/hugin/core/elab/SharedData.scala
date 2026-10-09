package hugin.core
package elab

import hugin.syntax.{Tree, TreeOps}
import hugin.syntax.Trees.*
import hugin.util.*

/** Shared data declarations (reference: meta/families, shared data; `docs/design/stage-polymorphism.md`,
 *  issue #80). `T ā : data.` with constructors `cᵢ : σ̄ᵢ -> T ā.` declares under each name two constants
 *  of the existing core, linked by [[SharedLink]]:
 *
 *  - a meta inductive family `T : Type → … → Type` with constructors `cᵢ : {ā : Type} → σ̄ᵢ → T ā`;
 *  - an object family (or type) `T : ⇑type → … → ⇑type` with fact constructors `cᵢ : {ā : ⇑type} → ⇑(σ̄ᵢ → T ā)`;
 *  - two meta functions by clauses, checked for coverage and termination like hand-written ones:
 *    `T.lift : (a₁ → ⇑b₁) → … → T ā → ⇑(T b̄)`, `T.lift f̄ (cᵢ x̄) = cᵢ (L[σ] x)…` (the fold into object code), and
 *    `T.reify : (a₁ → term) → … → T ā → term`, `T.reify ḡ (cᵢ x̄) = '( cᵢ $(R[σ] x)… )` (into `term` data).
 *
 *  The meta constants are the names in scope; a name is the object constant at an object position
 *  ([[sharedAt]], by the stage of the position, [[ElabState.stage]]). The constructors' arguments are
 *  parameters, base types and shared types (E0920), the type is used at its parameters only (E0921), it
 *  is closed (E0922, E0923) and declared at the top level of a file (E0923). */
trait SharedData:
  self: Elaborator =>
  import core.*

  /** The constant `id` at stage `st`: its counterpart if it is a shared constant of the other stage. */
  def sharedAt(id: Int, st: Stage): Int = globals(id).shared match
    case Some(l) if l.side != st => l.counterpart
    case _ => id

  /** The link of a shared meta family. */
  def sharedFamily(id: Int): Option[SharedLink] =
    globals(id).shared.filter(l => l.side == Stage.S1 && globals(id).kind.isInstanceOf[GlobalKind.Inductive])

  /** The shared family a declaration without definition returns, if it declares one of its constructors. */
  def sharedResult(d: Decl): Option[Int] =
    if d.sup.isDefined || d.params.nonEmpty || state.functionNames(d.name.name) then None
    else TreeOps.headName(TreeOps.codomain(d.tpe)).flatMap(n => lookupGlobal(n.name)).filter(sharedFamily(_).isDefined)

  // ---------------------------------------------------------------- declarations

  def isDataDecl(d: Decl): Boolean = d.tpe match
    case Keyword(Kw.Data) => true
    case _ => false

  /** `T ā : data.`: the meta family, the object family, and the declarations of `T.lift` and `T.reify`
   *  (their clauses follow once the constructors are declared, [[DerivedFunctions]]). */
  def elabData(d: Decl): Unit =
    d.params.foreach {
      case Param.VarParam(_) =>
      case Param.Typed(_, _, sp) => fail(SharedProblem.NotUniform(d.name.name, "the parameters of a shared type are variables", sp))
      case Param.Malformed(t) => syntaxError(t.span)
    }
    val sp = d.tpe.span
    val metaType = d.params.foldRight(VarRef("Type")(sp): Tree)((_, acc) => Arrow(None, VarRef("Type")(sp), acc)(sp))
    val (mty, _, mkind) = side(Decl(d.name, Nil, metaType, None, None)(d.span), Stage.S1)
    val (oty, ost, okind) = side(Decl(d.name, d.params, Keyword(Kw.Type)(sp), None, None)(d.span), Stage.S0)
    val m = declare(d.name, mty, Stage.S1, mkind, d.span)
    val o = declareHidden(d.name, oty, ost, okind, d.span)
    link(m, o)
    state.sharedDeclared :+= m
    globals(m).shared.get.lift = declareShared(m, lift = true)
    // `T.reify` needs `term`: in the prelude, declared after `list` (see [[defineSharedFunctions]])
    if reflectiveGlobals.isDefined then globals(m).shared.get.reify = declareShared(m, lift = false)

  /** A constructor `c : σ̄ -> T ā.` of the shared family `fam`: its meta and object constructors. */
  def elabSharedConstructor(d: Decl, fam: Int): Unit =
    val famName = globals(fam).name
    if !scope.get(famName).contains(fam) then
      fail(SharedProblem.ConstructorElsewhere(d.name.name, famName, d.name.span, globals(fam).declSpan))
    val (mty, _, mkind) = side(d, Stage.S1)
    if mkind != GlobalKind.Constructor(fam) then fail(SharedProblem.NotUniform(famName, s"not `$famName` at its parameters", d.tpe.span))
    checkShareable(d, fam, eval(Nil, mty))
    val (oty, ost, okind) = side(d, Stage.S0)
    val m = declare(d.name, mty, Stage.S1, mkind, d.span)
    addConstructor(fam, m)
    link(m, declareHidden(d.name, oty, ost, okind, d.span))

  /** The type, stage and kind of a declaration at the meta stage (an inductive family or constructor) or
   *  at the object stage (an object family, type or constructor). */
  private def side(d: Decl, st: Stage): (Tm, Stage, GlobalKind) = atStage(st) {
    if st == Stage.S1 then
      constant(d, firstSuccess(List(true, false).map(inferred => () => declTypeWith(d, Stage.S1, inferred, Cxt.empty))))
    else constant(d, declTypeWith(d, Stage.S0, inferred = true, Cxt.empty))
  }

  private def link(m: Int, o: Int): Unit =
    globals(m).shared = Some(SharedLink(Stage.S1, o))
    globals(o).shared = Some(SharedLink(Stage.S0, m))

  // ---------------------------------------------------------------- restrictions

  /** E0920, E0921: the constructor `d` of type `ty` (its meta side) returns `fam` at distinct implicit
   *  parameters, and its arguments are parameters, base types or shared types (`fam` at the parameters). */
  private def checkShareable(d: Decl, fam: Int, ty: Val): Unit =
    val famName = globals(fam).name
    val (binders, result) = telescope(ty)
    val arity = telescope(globals(fam).ty)._1.length
    def notUniform(why: String, at: Span): Nothing = fail(SharedProblem.NotUniform(famName, why, at))
    val params = forceData(result) match
      case Val.Rigid(Head.Glob(f), sp) if f == fam =>
        val vs = sp.reverse.collect { case Elim.EApp(Val.Rigid(Head.Local(l), Nil), _) if binders(l)._2 == Icit.Impl => l }
        if vs.length != arity || vs.distinct.length != arity then
          notUniform(s"the result is not `$famName` at its parameters", TreeOps.codomain(d.tpe).span)
        vs
      case _ => notUniform(s"the result is not `$famName` at its parameters", TreeOps.codomain(d.tpe).span)
    val trees = argumentTypes(d.tpe)
    binders.zipWithIndex.collect { case ((_, Icit.Expl, a), l) => (a, l) }.zipWithIndex.foreach { case ((a, l), k) =>
      val at = trees.lift(k).map(_.span).getOrElse(d.tpe.span)
      def go(a: Val): Unit = forceData(a) match
        case Val.Rigid(Head.Local(x), Nil) if params.contains(x) =>
        case Val.Base(_, Stage.S1) =>
        case Val.Rigid(Head.Glob(g), sp) if sharedFamily(g).isDefined && sp.forall(_.isInstanceOf[Elim.EApp]) =>
          val args = sp.reverse.collect { case Elim.EApp(x, _) => x }
          if g == fam then
            val atParams = args.map(forceData).collect { case Val.Rigid(Head.Local(x), Nil) => x }
            if atParams != params then notUniform(s"`$famName` at other arguments than its parameters (polymorphic recursion)", at)
          else args.foreach(go)
        case other => fail(SharedProblem.NotShareable(d.name.name, famName, showVal(binders.take(l).map(_._1).reverse, other), at))
      go(a)
    }

  /** The type of each explicit argument of a constructor's declared type, as written. */
  private def argumentTypes(tpe: Tree): List[Tree] =
    TreeOps.flattenArrow(tpe)._1.flatMap { (label, dom) =>
      val (ns, t) = binders(label, dom)
      List.fill(ns.length)(t)
    }
