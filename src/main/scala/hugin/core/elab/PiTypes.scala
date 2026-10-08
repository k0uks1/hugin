package hugin.core
package elab

import hugin.syntax.Tree
import hugin.syntax.Trees.*
import hugin.util.*
import hugin.util.diagnostics.{Code as DiagCode, Legacy}

/** Π types. Three surface forms are distinguished:
 *
 *  - an arrow ending in `rel` is always an **object relation type** (stage 0), also inside meta types
 *    (`edge : node -> node -> rel` in a signature is `⇑($node -> $node -> rel)`);
 *  - an arrow checked against `Type` is a **meta function type**: object types written as domains or
 *    codomain are lifted (`item -> prop` is `⇑item -> ⇑prop`, a formula function), base types become the
 *    meta primitives (Kovács's rule: the stage of a Π is the stage of its universe);
 *  - an arrow whose type is inferred (a declaration's type) takes the stage of its parts: all object
 *    types give an object constructor type, any meta part makes it a meta function type;
 *
 *  and `{A : T} -> B` is an implicit (meta) Π. */
trait PiTypes:
  self: Elaborator =>
  import core.*

  /** `A₁ -> … -> rel`. */
  def endsInRel(t: Tree): Boolean = t match
    case Arrow(_, _, cod) => endsInRel(cod)
    case Parens(i) => endsInRel(i)
    case Keyword(Kw.Rel) => true
    case _ => false

  /** Binder names of an arrow's domain: `(x : A)`, `(A B : T)`, or the label of `(l : A) -> …`. */
  def binders(label: Option[Ident], dom: Tree): (List[(Name, Span)], Tree) = (label, dom) match
    case (Some(l), _) => (List((l.name, l.span)), dom)
    case (None, Ascribe(names, a)) if boundNames(names).isDefined =>
      (boundNames(names).get.map(x => (nameOf(x), x.span)), a)
    case _ => (List(("_", dom.span)), dom)

  /** Builds `(n₁ : A) -> … -> (nₖ : A) -> body` for binders sharing the domain `dom` (elaborated in `c`). */
  private def piChain(c: Cxt, ns: List[Name], i: Icit, dom: Tm, st: Stage, scoped: Boolean)(body: Cxt => Tm): Tm =
    def go(cc: Cxt, rest: List[Name]): Tm = rest match
      case Nil => body(cc)
      case n :: more =>
        val inner = if scoped then bind(cc, n, ev(c, dom), st) else newBinder(cc, n, ev(c, dom), st)
        Tm.Pi(n, i, Tm.shift(dom, cc.lvl - c.lvl), go(inner, more))
    go(c, ns)

  /** An object arrow `A₁ -> … -> B` (stage 0). Column labels are not in scope: the object level is not
   *  dependent. */
  def objectArrow(c: Cxt, t: Tree): Tm = t match
    case Parens(i) => objectArrow(c, i)
    case Arrow(label, dom, cod) =>
      val (ns, d) = binders(label, dom)
      val dt = columnType(c, d)
      if force(ev(c, dt)) == Val.U0 then
        fail(
          Legacy.error(DiagCode.E0908, "relations and constructors cannot take object types as arguments", d.span, "a type")
            .withNote("the object level is first order; families of relations are meta functions returning relations")
        )
      piChain(c, ns.map(_._1), Icit.Expl, dt, Stage.S0, scoped = false)(objectArrow(_, cod))
    case other => check(c, other, Val.U0, Stage.S0)

  /** An arrow whose type is inferred: the stage follows from its parts. */
  def inferArrow(c: Cxt, label: Option[Ident], dom: Tree, cod: Tree, span: Span): (Tm, Val, Stage) =
    val (ns, d) = binders(label, dom)
    val (dt, sd, ud) = d match
      case _: BoundType => (columnType(c, d), Stage.S0, Val.U0) // validated at the object level
      case _ => metaBinderOverTypes(c, inferU(c, d))
    def go(cc: Cxt, rest: List[Name]): (Tm, Stage, Val) = rest match
      case Nil => inferU(cc, cod)
      case n :: more =>
        val dom = Tm.shift(dt, cc.lvl - c.lvl)
        val inner = if sd == Stage.S1 then bind(cc, n, ev(c, dt), sd) else newBinder(cc, n, ev(c, dt), sd)
        val (bt, sb, ub) = go(inner, more)
        mixedPi(cc, span, n, dom, sd, ud, bt, sb, ub)
    val (tm, s, u) = go(c, ns.map(_._1))
    (tm, u, s)

  /** A binder over object types is a meta binder: `(A : type) -> …` is `(A : ⇑type) -> …`. */
  private def metaBinderOverTypes(c: Cxt, d: (Tm, Stage, Val)): (Tm, Stage, Val) =
    if force(ev(c, d._1)) == Val.U0 then (Tm.Lift(d._1), Stage.S1, Val.U1(Level.zero)) else d

  /** `(n : dom) -> body` from a domain at stage `sd` and a body at stage `sb` (in context `c`, the body
   *  under one more binder): object if both are object types, otherwise a meta Π whose object parts are
   *  lifted. A meta type cannot depend on an object variable. */
  private def mixedPi(c: Cxt, span: Span, n: Name, dom: Tm, sd: Stage, ud: Val, body: Tm, sb: Stage, ub: Val): (Tm, Stage, Val) =
    if sd == Stage.S0 && sb == Stage.S0 then (Tm.Pi(n, Icit.Expl, dom, body), Stage.S0, Val.U0)
    else
      if sd == Stage.S0 && occurs(0, body) then
        fail(Legacy.error(DiagCode.E0902, "a meta type cannot depend on object code", span, s"`$n` is object code"))
      val l = levels.fresh()
      requireLe(c, span, ud, l)
      requireLe(c, span, ub, l)
      val dom1 = if sd == Stage.S0 then liftType(c, dom) else dom
      val body1 = if sb == Stage.S0 then liftType(bind(c, n, ev(c, dom1), Stage.S1), body) else body
      (Tm.Pi(n, Icit.Expl, dom1, body1), Stage.S1, Val.U1(l))

  /** An arrow checked against `Type l`: domains and codomain are meta types. */
  def checkMetaArrow(c: Cxt, label: Option[Ident], dom: Tree, cod: Tree, l: Level): Tm =
    val (ns, d) = binders(label, dom)
    val dt = check(c, d, Val.U1(l), Stage.S1)
    piChain(c, ns.map(_._1), Icit.Expl, dt, Stage.S1, scoped = true)(check(_, cod, Val.U1(l), Stage.S1))

  /** `{A B : T} -> B` checked against `Type l`. */
  def checkImplicitPi(c: Cxt, names: List[Tree], dom: Tree, cod: Tree, l: Level): Tm =
    val dt = check(c, dom, Val.U1(l), Stage.S1)
    piChain(c, names.map(nameOf), Icit.Impl, dt, Stage.S1, scoped = true)(check(_, cod, Val.U1(l), Stage.S1))
