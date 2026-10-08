package hugin.core
package elab

import hugin.syntax.Tree
import hugin.syntax.Trees.*
import hugin.util.*
import hugin.util.diagnostics.Code as DiagCode

/** Declarations and definitions (REDESIGN §6.2, §6.4):
 *
 *  - `x : A.` declares a constant. Classification by the universe of its type: an object type (`expr :
 *    type.`), object constructor (`lam : name -> expr -> expr.`) or relation (`edge : node -> node ->
 *    rel.`) when the type is an object type; otherwise a meta-level constant. Free uppercase variables
 *    of the type are implicit binders (`nil : list A.` is `nil : {A : ⇑type} -> ⇑$(list A)`); head
 *    parameters `list A : type.` are explicit binders over object types.
 *  - `x : A = e.`, `x = e.` and `f params = e.` are meta-level definitions (with an inferred type in the
 *    last two forms); after `f : A.`, `f params = e.` is a clause of the function `f` ([[Clauses]]).
 *  - a meta declaration without definition is an inductive family, a constructor, a function (if it has
 *    clauses) or a postulate ([[Inductives.classifyMetaConstant]]).
 */
trait Declarations:
  self: Elaborator =>
  import core.*

  /** Adds a global and its item; a name may be declared once per module. */
  def declare(name: Ident, ty: Tm, stage: Stage, kind: GlobalKind, declSpan: Span = Span.NoSpan): Int =
    scope.get(name.name).filter(id => globals(id).pending && globals(id).declSpan == declSpan) match
      case Some(id) if stage == Stage.S0 => completePending(id, ty, kind)
      case Some(_) =>
        scope.remove(name.name) // not the object constant its syntax suggested
        declareNew(name, ty, stage, kind, declSpan)
      case None => declareNew(name, ty, stage, kind, declSpan)

  private def declareNew(name: Ident, ty: Tm, stage: Stage, kind: GlobalKind, declSpan: Span): Int =
    if scope.contains(name.name) then
      fail(ElabProblem.DuplicateMember(name.name, name.span, globals(scope(name.name)).span))
    val objectLike = stage == Stage.S0 || kind.isInstanceOf[GlobalKind.Family]
    val gname = if objectLike then file.objectName(name.name) else name.name
    val id = addGlobal(GlobalEntry(gname, eval(Nil, ty), ty, stage, kind, name.span, declSpan))
    scope(name.name) = id
    items += CoreItem.GlobalItem(id)
    id

  /** `(x₁ : A₁) -> … -> body` (or implicit) over binders `(name, type)`, outermost first. */
  def pis(binders: List[(Name, Tm)], i: Icit, body: Tm): Tm = binders.foldRight(body)((b, acc) => Tm.Pi(b._1, i, b._2, acc))

  def lams(binders: List[(Name, Tm)], body: Tm): Tm = binders.foldRight(body)((b, acc) => Tm.Lam(b._1, Icit.Expl, acc))

  /** Binds the parameters of a declaration head: `(x : A)` has type A, `X` the type given by `untyped`. */
  def bindParams(c: Cxt, params: List[Param], untyped: (Cxt, VarRef) => Tm): (Cxt, List[(Name, Tm)]) =
    var cc = c
    val out = params.map { p =>
      val (n, ty, origin) = p match
        case Param.VarParam(v) => (v.name, untyped(cc, v), BinderOrigin.Plain)
        case Param.Typed(n, t, _) => (nameOf(n), checkType(cc, t, Stage.S1), BinderOrigin.Param(n.span, t))
      cc = bind(cc, n, ev(cc, ty), Stage.S1, origin)
      (n, ty)
    }
    (cc, out)

  /** `X` in `list X : type.` ranges over object types. */
  private val objectTypeParam: (Cxt, VarRef) => Tm = (_, _) => Tm.Lift(Tm.U0)

  /** Binds the implicit binders of a declaration: its free uppercase variables, of unknown meta types. */
  def bindImplicits(vs: List[VarRef], base: Cxt = Cxt.empty): (Cxt, List[(Name, Tm)]) =
    var c = base
    val out = vs.distinctBy(_.name).filterNot(v => base.scope.contains(v.name)).map { v =>
      val ty = freshType(c, Stage.S1, v.span, s"the type of `${v.name}`")
      c = bind(c, v.name, ev(c, ty), Stage.S1)
      (v.name, ty)
    }
    (c, out)

  /** The context of a declaration's type: its implicit binders, then its parameters. */
  private def declContext(d: Decl, base: Cxt): (Cxt, List[(Name, Tm)], List[(Name, Tm)]) =
    val paramNames = d.params.map(_.nameString).toSet
    val paramTypes = d.params.collect { case Param.Typed(_, t, _) => t }
    val (c, imps) = bindImplicits((d.tpe :: paramTypes).flatMap(freeVars(_, paramNames)), base)
    val (c2, ps) = bindParams(c, d.params, objectTypeParam)
    (c2, imps, ps)

  /** The type of a declaration and the stage of the declared constant.
   *
   *  The type is inferred, which classifies the constant (REDESIGN §6.2): an object constant if its type
   *  is the type of an object type, constructor or relation ([[isObjectConstantType]]), otherwise the type
   *  is checked as a meta type (so `f : int -> int.` is a meta function on meta integers). The types of
   *  implicit binders are unknown: they are tried as meta types first (`vcons : A -> vec A N -> …`), then
   *  as object types (`cons : A -> list A -> list A.` with `list : type -> type`). The first alternative
   *  that elaborates wins; failed ones are undone. */
  def declType(d: Decl, base: Cxt = Cxt.empty): (Tm, Stage) =
    val alternatives =
      for
        unknown <- List(Stage.S1, Stage.S0)
        inferred <- List(true, false)
      yield () => declTypeWith(d, unknown, inferred, base)
    firstSuccess(alternatives)

  def firstSuccess[A](alternatives: List[() => A]): A =
    var firstError: Option[ElabError] = None
    alternatives.iterator
      .map { alt =>
        try Some(undoOnFailure(alt()))
        catch
          case e: ElabError =>
            if firstError.isEmpty then firstError = Some(e)
            None
      }
      .collectFirst { case Some(r) => r }
      .getOrElse(throw firstError.get)

  private def declTypeWith(d: Decl, unknown: Stage, inferred: Boolean, base: Cxt): (Tm, Stage) =
    state.unknownTypesAre = unknown
    try
      val (c2, imps, ps) = declContext(d, base)
      val (body, st) =
        if inferred then
          val (b, s, _) = inferU(c2, d.tpe)
          if s == Stage.S0 && !isObjectConstantType(ev(c2, b)) || s == Stage.S1 && !objectPartsValid(ev(c2, b)) then
            error(DiagCode.E0901, "not the type of an object constant", d.tpe.span)
          (b, s)
        else (checkType(c2, d.tpe, Stage.S1), Stage.S1)
      if imps.isEmpty && ps.isEmpty then (body, st)
      else
        val body1 = if st == Stage.S0 then liftType(c2, body) else body
        (pis(imps, Icit.Impl, pis(ps, Icit.Expl, body1)), Stage.S1)
    finally state.unknownTypesAre = Stage.S1

  def elabDecl(d: Decl): Unit =
    if isStructDecl(d) then elabStruct(d)
    else if d.sup.isDefined then elabRefinement(d)
    else elabPlainDecl(d)

  private def elabPlainDecl(d: Decl): Unit =
    d.defn match
      case None =>
        val (ty, st) = declType(d)
        val zty = zonk(Nil, 0, ty)
        val tv = eval(Nil, zty)
        val kind =
          if st == Stage.S0 then GlobalKind.Object(objectDecl(d, tv))
          else familyKind(d, tv).getOrElse(classifyMetaConstant(d, tv))
        val id = declare(d.name, zty, st, kind, d.span)
        kind match
          case GlobalKind.Constructor(fam) => addConstructor(fam, id)
          case _ =>
      case Some(e) =>
        val (ty, tm) = declDefinition(Cxt.empty, d, e)
        define(d.name, ty, tm, d.span)

  /** `x params : A = e.` in context `c`: its type and definition. Checking `e` against the full type
   *  introduces the implicit lambdas. */
  def declDefinition(c: Cxt, d: Decl, e: Tree): (Tm, Tm) =
    val (c2, imps, ps) = declContext(d, c)
    val ty = pis(imps, Icit.Impl, pis(ps, Icit.Expl, checkType(c2, d.tpe, Stage.S1)))
    val tyV = ev(c, ty)
    val builtin = (e, d.tpe) match
      case (_: Builtin, Keyword(Kw.Type)) => d.params.isEmpty
      case _ => false
    val body = if builtin then definingBuiltin(check(c, e, tyV, Stage.S1)) else check(c, asLambda(d.params, e), tyV, Stage.S1)
    (ty, ascribed(tyV, e.span, body))

  /** A module ascribed a signature with `%fact` fields (`m : sig = e.`) must pass fact constructors for
   *  them ([[Tm.Require]]; the other requirements concern functor applications). */
  private def ascribed(ty: Val, span: Span, t: Tm): Tm = force(ty) match
    case rt: Val.RecTy if rt.reqs.exists(_.isInstanceOf[SigReq.Fact]) =>
      Tm.Require(rt.reqs.filter(_.isInstanceOf[SigReq.Fact]), span, t)
    case _ => t

  def define(name: Ident, ty: Tm, tm: Tm, declSpan: Span): Int =
    val ztm = zonk(Nil, 0, tm)
    declare(name, zonk(Nil, 0, ty), Stage.S1, GlobalKind.Definition(ztm, eval(Nil, ztm)), declSpan)

  /** `f params = e.` without a declaration of `f`: a definition with an inferred type. (After a
   *  declaration, it is a clause of the declared function.) */
  def elabDef(name: Ident, params: List[Param], rhs: Tree, span: Span): Unit =
    val (ty, tm) = definition(Cxt.empty, params, rhs)
    define(name, ty, tm, span)

  /** `f params = e.` in context `c`: its inferred type and its definition. Free uppercase variables of
   *  the parameters' types are implicit binders (`select (p : A -> prop) (r : A -> rel) = …`), of unknown
   *  meta types first, then of object types (as for declarations). */
  def definition(c: Cxt, params: List[Param], rhs: Tree): (Tm, Tm) =
    val paramNames = params.map(_.nameString).toSet
    val free = params.collect { case Param.Typed(_, t, _) => t }.flatMap(freeVars(_, paramNames ++ c.scope.keySet))
    if free.isEmpty then definitionWith(c, Nil, params, rhs)
    else
      firstSuccess(List(Stage.S1, Stage.S0).map { unknown => () =>
        state.unknownTypesAre = unknown
        try definitionWith(c, free, params, rhs)
        finally state.unknownTypesAre = Stage.S1
      })

  private def definitionWith(c: Cxt, free: List[VarRef], params: List[Param], rhs: Tree): (Tm, Tm) =
    val (ci, imps) = bindImplicits(free, c)
    val (cp, ps) = bindParams(ci, params, (cc, v) => freshType(cc, Stage.S1, v.span, s"the type of `${v.name}`"))
    val (body, bty) = inferS(cp, rhs, Stage.S1)
    val ty = pis(imps, Icit.Impl, pis(ps, Icit.Expl, quote(cp.lvl, bty)))
    val tm = imps.foldRight(lams(ps, body))((b, acc) => Tm.Lam(b._1, Icit.Impl, acc))
    (ty, tm)

  private def asLambda(params: List[Param], rhs: Tree): Tree = params.foldRight(rhs) { (p, acc) =>
    p match
      case Param.VarParam(v) => Lambda(v, None, acc)(v.span.to(acc.span))
      case Param.Typed(n, t, sp) => Lambda(n, Some(t), acc)(sp.to(acc.span))
  }
