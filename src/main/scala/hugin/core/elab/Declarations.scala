package hugin.core
package elab

import hugin.syntax.Tree
import hugin.syntax.Trees.*
import hugin.util.*

/** Declarations and definitions (reference: meta/universes, meta/clauses):
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
    val id = declareHidden(name, ty, stage, kind, declSpan)
    scope(name.name) = id
    id

  /** Adds a global and its item without a name in scope (the object side of a shared declaration, which
   *  is found through its meta side, [[SharedData]]). */
  def declareHidden(name: Ident, ty: Tm, stage: Stage, kind: GlobalKind, declSpan: Span): Int =
    val objectLike = stage == Stage.S0 || kind.isInstanceOf[GlobalKind.Family]
    val gname = if objectLike then file.objectName(name.name) else name.name
    val id = addGlobal(GlobalEntry(gname, eval(Nil, ty), ty, stage, kind, name.span, declSpan))
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
        case Param.Malformed(t) => syntaxError(t.span)
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

  /** The context of a declaration's type: its implicit binders, then its parameters (an untyped one is
   *  typed by `untyped`). */
  private def declContext(d: Decl, base: Cxt, untyped: (Cxt, VarRef) => Tm = objectTypeParam): (Cxt, List[(Name, Tm)], List[(Name, Tm)]) =
    val paramNames = d.params.map(_.nameString).toSet
    val paramTypes = d.params.collect { case Param.Typed(_, t, _) => t }
    val (c, imps) = bindImplicits((d.tpe :: paramTypes).flatMap(freeVars(_, paramNames)), base)
    val (c2, ps) = bindParams(c, d.params, untyped)
    (c2, imps, ps)

  /** An untyped parameter of a definition `f X : A = e.` has an unknown type, inferred from its uses (as
   *  in `f X = e.`); of a type definition `t X : type = τ.` it ranges over object types. */
  private def definitionParam(d: Decl): (Cxt, VarRef) => Tm = d.tpe match
    case Keyword(Kw.Type) => objectTypeParam
    case _ => (cc, v) => freshType(cc, Stage.S1, v.span, s"the type of `${v.name}`")

  /** The type of a declaration and the stage of the declared constant.
   *
   *  The type is inferred, which classifies the constant (reference: meta/universes): an object constant if its type
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

  def declTypeWith(d: Decl, unknown: Stage, inferred: Boolean, base: Cxt): (Tm, Stage) =
    state.unknownTypesAre = unknown
    try
      val (c2, imps, ps) = declContext(d, base)
      val (body, st) =
        if inferred then
          val (b, s, _) = atStage(positionStage(c2, d.tpe, unknown))(inferU(c2, d.tpe))
          if s == Stage.S0 && !isObjectConstantType(ev(c2, b)) || s == Stage.S1 && !objectPartsValid(ev(c2, b)) then
            fail(TypeProblem.NotObjectConstantType(d.tpe.span))
          (b, s)
        else (checkType(c2, d.tpe, Stage.S1), Stage.S1)
      if imps.isEmpty && ps.isEmpty then (body, st)
      else
        val body1 = if st == Stage.S0 then liftType(c2, body) else body
        (pis(imps, Icit.Impl, pis(ps, Icit.Expl, body1)), Stage.S1)
    finally state.unknownTypesAre = Stage.S1

  /** The stage of the positions in a declared type whose stage is inferred, where a name of a shared data
   *  declaration denotes its constant at that stage: the stage of the declared constant's result. A type
   *  ending in an object type (`wrap : list int -> box.`) declares an object constant, so its shared types
   *  are object types; otherwise they are meta types (`size : list int -> int.`: a meta function). With
   *  unknown types taken as object types, object. */
  private def positionStage(c: Cxt, tpe: Tree, unknown: Stage): Stage =
    if unknown == Stage.S0 then Stage.S0
    else
      tentatively {
        try inferU(c, hugin.syntax.TreeOps.codomain(tpe))._2
        catch case _: ElabError => Stage.S1
      }

  def elabDecl(d: Decl): Unit =
    if isDataDecl(d) then elabData(d)
    else if isStructDecl(d) then elabStruct(d)
    else if d.sup.isDefined then elabRefinement(d)
    else elabPlainDecl(d)

  private def elabPlainDecl(d: Decl): Unit =
    d.defn match
      case None if sharedResult(d).isDefined => elabSharedConstructor(d, sharedResult(d).get)
      case None =>
        val (zty, st, kind) = constant(d, declType(d))
        val id = declare(d.name, zty, st, kind, d.span)
        kind match
          case GlobalKind.Constructor(fam) => addConstructor(fam, id)
          case _ =>
      case Some(Builtin(Ident("symbol"))) if d.params.isEmpty && d.tpe == VarRef("Type")(d.tpe.span) =>
        declare(d.name, Tm.U1(Level.zero), Stage.S1, GlobalKind.Symbols, d.span)
      case Some(b @ Builtin(Ident(k))) if PrimOp.byKey(k).isDefined && d.params.isEmpty =>
        val (c2, imps, _) = declContext(d, Cxt.empty)
        val ty = zonk(Nil, 0, pis(imps, Icit.Impl, checkType(c2, d.tpe, Stage.S1)))
        val op = PrimOp.byKey(k).get
        declare(d.name, ty, Stage.S1, GlobalKind.Primitive(op, primitiveCtors(op, eval(Nil, ty), b.span)), d.span)
      case Some(e) =>
        val (ty, tm) = declDefinition(Cxt.empty, d, e)
        define(d.name, ty, tm, d.span)

  /** The declared constant `d` of type `ty` at stage `st`: its zonked type, its stage and its kind. */
  def constant(d: Decl, typed: (Tm, Stage)): (Tm, Stage, GlobalKind) =
    val (ty, st) = typed
    val zty = zonk(Nil, 0, ty)
    val tv = eval(Nil, zty)
    val kind =
      if st == Stage.S0 then GlobalKind.Object(objectDecl(d, tv))
      else familyKind(d, tv).getOrElse(classifyMetaConstant(d, tv))
    (zty, st, kind)

  /** `x params : A = e.` in context `c`: its type and definition. Checking `e` against the full type
   *  introduces the implicit lambdas. With both implicit binders and parameters (`ident (x : A) : A = x.`),
   *  `e` is checked in the declaration's context, where the implicit binders are in scope, as in
   *  `f (x : A) = e.`. */
  def declDefinition(c: Cxt, d: Decl, e: Tree): (Tm, Tm) =
    val (c2, imps, ps) = declContext(d, c, definitionParam(d))
    val result = checkType(c2, d.tpe, Stage.S1)
    val ty = pis(imps, Icit.Impl, pis(ps, Icit.Expl, result))
    val tyV = ev(c, ty)
    val builtin = (e, d.tpe) match
      case (_: Builtin, Keyword(Kw.Type)) => d.params.isEmpty
      case _ => false
    val body =
      if builtin then definingBuiltin(check(c, e, tyV, Stage.S1))
      else if imps.nonEmpty && ps.nonEmpty then
        val inner = check(c2, e, ev(c2, result), Stage.S1)
        imps.foldRight(lams(ps, inner))((b, acc) => Tm.Lam(b._1, Icit.Impl, acc))
      else typeBindersOutOfScope(d, e)(check(c, asLambda(d.params, e), tyV, Stage.S1))
    if !builtin then checkObjectFragments(c, body, tyV)
    (ty, body)

  /** `f : (x : A) -> B = e.` where `e` uses `x`: the binders of a declared type do not scope over the
   *  definition (E0916), which should be written `f (x : A) : B = e.` */
  private def typeBindersOutOfScope[A](d: Decl, e: Tree)(elab: => A): A =
    val (binders, rest) = namedBinders(d.tpe)
    val names = binders.map(_._1.name).filterNot(n => scope.contains(n) || file.parent.contains(n)).toSet
    if d.params.nonEmpty || e.isInstanceOf[Lambda] then elab
    else
      uses(e, names).headOption match
        case None => elab
        case Some(use) =>
          val header = d.name.span.to(d.tpe.span)
          val params = binders.map((l, dom) => s"(${l.name} : ${dom.span.text})").mkString(" ")
          val rewritten = s"${d.name.name} $params : ${rest.span.text}"
          fail(ElabProblem.TypeBinderInDefinition(use.span.text, use.span, header, rewritten))

  /** The uses of the names `ns` in `t`, outside lambdas binding them. */
  private def uses(t: Any, ns: Set[Name]): List[Tree] = t match
    case _ if ns.isEmpty => Nil
    case i @ Ident(n) if ns(n) => List(i)
    case v @ VarRef(n) if ns(n) => List(v)
    case Lambda(p, ann, b) => uses(ann, ns) ++ uses(b, ns - nameOf(p))
    case p: Product => p.productIterator.toList.flatMap(uses(_, ns))
    case it: Iterable[?] => it.toList.flatMap(uses(_, ns))
    case _ => Nil

  /** The leading named binders `(x : A) -> …` of a type and the rest of it. */
  private def namedBinders(t: Tree): (List[(Ident, Tree)], Tree) = t match
    case Arrow(Some(l), dom, cod) =>
      val (bs, rest) = namedBinders(cod)
      ((l, dom) :: bs, rest)
    case Parens(i) if namedBinders(i)._1.nonEmpty => namedBinders(i)
    case other => (Nil, other)

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
    checkObjectFragments(cp, body, bty)
    val ty = pis(imps, Icit.Impl, pis(ps, Icit.Expl, quoteFolded(cp.lvl, bty)))
    val tm = imps.foldRight(lams(ps, body))((b, acc) => Tm.Lam(b._1, Icit.Impl, acc))
    (ty, tm)

  private def asLambda(params: List[Param], rhs: Tree): Tree = params.foldRight(rhs) { (p, acc) =>
    p match
      case Param.VarParam(v) => Lambda(v, None, acc)(v.span.to(acc.span))
      case Param.Typed(n, t, sp) => Lambda(n, Some(t), acc)(sp.to(acc.span))
      case Param.Malformed(t) => syntaxError(t.span)
  }

  /** The constructors primitive `op` of type `ty` builds; E0103 if `ty` is not its type
   *  ([[hugin.core.Primitives]]). */
  private def primitiveCtors(op: PrimOp, ty: Val, span: Span): List[Int] =
    val (binders, result) = telescope(ty)
    def isSym(v: Val) = forceData(v) match
      case Val.Rigid(Head.Glob(id), Nil) => globals(id).kind == GlobalKind.Symbols
      case _ => false
    def isString(v: Val) = forceData(v) == Val.Base(hugin.obj.BaseType.StringT, Stage.S1)
    def ctorsOf(v: Val, check: Int => Boolean): Option[List[Int]] = forceData(v) match
      case Val.Rigid(Head.Glob(id), sp) =>
        globals(id).kind match
          case GlobalKind.Inductive(cs) if cs.length == 2 && check(id) && sp.forall {
                case Elim.EApp(a, _) => isString(a)
                case _ => false
              } =>
            Some(cs)
          case _ => None
      case _ => None
    val doms = binders.map(_._3)
    val found = op match
      case PrimOp.Same if binders.map(_._2) == List(Icit.Impl, Icit.Expl, Icit.Expl) =>
        ctorsOf(result, id => telescope(globals(id).ty)._1.isEmpty)
      case PrimOp.Derived if doms.length == 1 && isSym(doms.head) => ctorsOf(result, id => telescope(globals(id).ty)._1.isEmpty)
      case PrimOp.Labels if doms.length == 1 && isSym(doms.head) => ctorsOf(result, id => telescope(globals(id).ty)._1.length == 1)
      case PrimOp.Derive if doms.length == 2 && isSym(doms(0)) && isString(doms(1)) && isSym(result) => Some(Nil)
      case PrimOp.QAtom if binders.map(_._2) == List(Icit.Impl, Icit.Expl) => qatomCtors(doms(1), result)
      case _ => None
    val expected = op match
      case PrimOp.Same => "A -> A -> bool"
      case PrimOp.Labels => "sym -> list string"
      case PrimOp.Derived => "sym -> bool"
      case PrimOp.Derive => "sym -> string -> sym"
      case PrimOp.QAtom => "quoted A -> formula"
    found.getOrElse(fail(ElabProblem.PrimitiveType(op.key, expected, span)))

  /** `fatom`, `tapp` and `qterm` for `qatom : quoted A -> formula`: the domain is an inductive family with
   *  one constructor (`qterm`) whose argument has a constructor `tapp`, the result one with `fatom`. */
  private def qatomCtors(dom: Val, result: Val): Option[List[Int]] =
    def ctors(v: Val): List[Int] = forceData(v) match
      case Val.Rigid(Head.Glob(id), _) =>
        globals(id).kind match
          case GlobalKind.Inductive(cs) => cs
          case _ => Nil
      case _ => Nil
    def named(cs: List[Int], n: String) = cs.find(globals(_).name == n)
    for
      qterm <- ctors(dom) match
        case List(q) => Some(q)
        case _ => None
      term <- telescope(globals(qterm).ty)._1.collectFirst { case (_, Icit.Expl, d) => d }
      tapp <- named(ctors(term), "tapp")
      fatom <- named(ctors(result), "fatom")
    yield List(fatom, tapp, qterm)
