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
 *    `T.reify : (a₁ → term) → … → T ā → term`, `T.reify ḡ (cᵢ x̄) = '{ cᵢ $(R[σ] x)… }` (into `term` data).
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
   *  (their clauses follow once the constructors are declared, [[defineSharedFunctions]]). */
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
    globals(m).shared.get.lift = derivedDecl(m, "lift", (a, b) => Arrow(None, a, LiftE(b)(sp))(sp), o => LiftE(o)(sp))

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
    state.sharedConstructors += m -> d

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

  /** `T.lift` or `T.reify`, declared: `(a₁ → E a₁ b₁) → … → T ā → R`, with `elem` building the type of an
   *  element function and `result` the result type from the object type `T b̄`. */
  private def derivedDecl(m: Int, what: String, elem: (Tree, Tree) => Tree, result: Tree => Tree): Int =
    val g = globals(m)
    val sp = g.declSpan
    val n = telescope(g.ty)._1.length
    val as = (1 to n).map(i => VarRef(s"A$i")(sp): Tree).toList
    val bs = (1 to n).map(i => VarRef(s"B$i")(sp): Tree).toList
    def applied(head: Int, args: List[Tree]): Tree = args.foldLeft(SymRef(head, g.name)(sp): Tree)(Apply(_, _)(sp))
    val metaT = applied(m, as)
    val objT = applied(g.shared.get.counterpart, bs)
    val tpe = as.zip(bs).foldRight(Arrow(None, metaT, result(objT))(sp): Tree)((ab, acc) => Arrow(None, elem(ab._1, ab._2), acc)(sp))
    val name = Ident(s"${g.name}.$what")(g.span)
    state.functionNames += name.name
    elabDecl(Decl(name, Nil, tpe, None, None)(sp))
    scope(name.name)

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
        if vs.length != arity || vs.distinct.length != arity then notUniform(s"the result is not `$famName` at its parameters", TreeOps.codomain(d.tpe).span)
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

  // ---------------------------------------------------------------- derived functions

  /** The clauses of `T.lift` and `T.reify` for the shared types of the file, now that their constructors
   *  are declared. `T.reify` is declared here: its type needs `term`, which may be declared after `T`
   *  (the prelude's `list` comes before the reflective types, whose sequences are lists). */
  def defineSharedFunctions(): Unit =
    val fams = state.sharedDeclared.filter(fam => scope.get(globals(fam).name).contains(fam))
    for fam <- fams; r <- reflectiveGlobals do
      val sp = globals(fam).declSpan
      val term = SymRef(r.term, "term")(sp)
      try globals(fam).shared.get.reify = derivedDecl(fam, "reify", (a, _) => Arrow(None, a, term)(sp), _ => term)
      catch case e: ElabError => report(e)
    for fam <- fams do
      val link = globals(fam).shared.get
      val ctors = constructors(fam).flatMap(c => state.sharedConstructors.get(c).map((c, _)))
      if link.lift >= 0 then define(link.lift, ctors.map(liftClause(fam, link.lift, _)))
      if link.reify >= 0 then define(link.reify, ctors.map(reifyClause(fam, link.reify, _)))

  private def define(fn: Int, clauses: List[SurfaceClause]): Unit =
    val start = metas.length
    try
      undoOnFailure {
        if clauses.nonEmpty then elabFunction(fn, clauses)
        checkSolved(start)
      }
    catch case e: ElabError => report(e)

  /** The explicit arguments of the meta constructor `c` (type, level, written type) and the levels of the
   *  family's parameters in its type. */
  private def shape(c: Int, d: Decl): (List[(Val, Int, Option[Tree])], List[Int]) =
    val (binders, result) = telescope(globals(c).ty)
    val params = forceData(result) match
      case Val.Rigid(_, sp) => sp.reverse.collect { case Elim.EApp(Val.Rigid(Head.Local(l), Nil), _) => l }
      case _ => Nil
    val trees = argumentTypes(d.tpe)
    val args = binders.zipWithIndex.collect { case ((_, Icit.Expl, a), l) => (a, l) }.zipWithIndex.map { case ((a, l), k) => (a, l, trees.lift(k)) }
    (args, params)

  /** `T.lift F̄ (c X̄) = c (L[σ₁] X₁) …`: a parameter's element function spliced, a closed type by the rule
   *  Lift (base types persisted, shared types lifted), an open shared type by its `lift`. */
  private def liftClause(fam: Int, fn: Int, ctor: (Int, Decl)): SurfaceClause =
    derivedClause(fam, fn, ctor, "F") { (fs, args) =>
      args.foldLeft(SymRef(sharedAt(ctor._1, Stage.S0), ctor._2.name.name)(Span.NoSpan): Tree) { case (acc, (x, kind)) =>
        val arg = kind match
          case ArgKind.Param(j) => SpliceE(Apply(fs(j), x)(Span.NoSpan))(Span.NoSpan)
          case ArgKind.Closed => x
          case ArgKind.Open(fn) => SpliceE(Apply(fn, x)(Span.NoSpan))(Span.NoSpan)
        Apply(acc, arg)(Span.NoSpan)
      }
    }

  /** `T.reify Ḡ (c X̄) = '{ c $(R[σ₁] X₁) … }`: a closed type by its reification at the hole. */
  private def reifyClause(fam: Int, fn: Int, ctor: (Int, Decl)): SurfaceClause =
    derivedClause(fam, fn, ctor, "G") { (gs, args) =>
      val app = args.foldLeft(SymRef(sharedAt(ctor._1, Stage.S0), ctor._2.name.name)(Span.NoSpan): Tree) { case (acc, (x, kind)) =>
        val hole = kind match
          case ArgKind.Param(j) => Apply(gs(j), x)(Span.NoSpan)
          case ArgKind.Closed => x
          case ArgKind.Open(fn) => Apply(fn, x)(Span.NoSpan)
        Apply(acc, SpliceE(hole)(Span.NoSpan))(Span.NoSpan)
      }
      quoteOf(app)
    }

  private def quoteOf(t: Tree): Tree = Quote(List(Rule(None, List(t), None)(Span.NoSpan)), terminated = false)(Span.NoSpan)

  private enum ArgKind:
    case Param(index: Int)
    case Closed
    case Open(fn: Tree)

  /** A clause of the derived function `fn` of `fam` for constructor `ctor`, with element functions named
   *  `prefix`ᵢ and the right-hand side built from them and the constructor's arguments. */
  private def derivedClause(fam: Int, fn: Int, ctor: (Int, Decl), prefix: String)(rhs: (List[Tree], List[(Tree, ArgKind)]) => Tree): SurfaceClause =
    val (c, d) = ctor
    val (args, params) = shape(c, d)
    val elems = params.indices.map(j => VarRef(s"$prefix${j + 1}")(Span.NoSpan): Tree).toList
    val reify = globals(fn).name.endsWith(".reify")
    def kindOf(a: Val, l: Int, tree: Option[Tree]): ArgKind = forceData(a) match
      case Val.Rigid(Head.Local(x), Nil) if params.contains(x) => ArgKind.Param(params.indexOf(x))
      case _ if closedType(a, l).isDefined => ArgKind.Closed
      case other => ArgKind.Open(elementFunction(other, l, tree, params, elems, reify))
    val xs = args.indices.map(k => VarRef(s"X${k + 1}")(Span.NoSpan): Tree).toList
    val pattern = xs.foldLeft(Ident(d.name.name)(Span.NoSpan): Tree)(Apply(_, _)(Span.NoSpan))
    val kinds = args.map((a, l, t) => kindOf(a, l, t))
    SurfaceClause(Ident(globals(fn).name)(globals(fam).span), elems :+ pattern, rhs(elems, xs.zip(kinds)), globals(fam).declSpan)

  /** The function a value of the open shared type `a` (over `l` variables, written `tree`) is lifted (or
   *  reified) with: `U.lift e₁ … eₙ`, a parameter by its element function, a closed type by the rule Lift
   *  in `(Y : τ) => Y` (`(Y : τ) => '{ $Y }`). */
  private def elementFunction(a: Val, l: Int, tree: Option[Tree], params: List[Int], elems: List[Tree], reify: Boolean): Tree =
    forceData(a) match
      case Val.Rigid(Head.Local(x), Nil) if params.contains(x) => elems(params.indexOf(x))
      case _ if closedType(a, l).isDefined =>
        val y = VarRef("Y")(Span.NoSpan)
        val written = tree.getOrElse(unsupportedAt(Span.NoSpan, "a closed argument type without its syntax"))
        Lambda(y, Some(written), if reify then quoteOf(SpliceE(y)(Span.NoSpan)) else y)(Span.NoSpan)
      case Val.Rigid(Head.Glob(g), sp) =>
        val link = sharedFamily(g).get
        val args = sp.reverse.collect { case Elim.EApp(x, _) => x }
        val trees = tree.map(t => TreeOps.flattenApp(unparenthesised(t))._2).getOrElse(Nil)
        val head = SymRef(if reify then link.reify else link.lift, globals(g).name)(Span.NoSpan): Tree
        args.zipWithIndex.foldLeft(head) { case (acc, (x, i)) =>
          Apply(acc, elementFunction(x, l, trees.lift(i), params, elems, reify))(Span.NoSpan)
        }
      case _ => unsupportedAt(Span.NoSpan, "an argument type that is not shared")

  private def unparenthesised(t: Tree): Tree = t match
    case Parens(i) => unparenthesised(i)
    case other => other
