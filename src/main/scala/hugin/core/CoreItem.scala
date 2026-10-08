package hugin.core

import hugin.util.{Origin, Span}

/** What one item of a module elaborated to. Object items are kept as elaborated (with the meta code they
 *  splice); the handover to the object level stages them ([[hugin.core.handover]]). */
enum CoreItem:
  case GlobalItem(id: Int)

  /** An object rule: its variables (with their object types, possibly unsolved metas) bind in the heads
   *  and the body. A `generic` rule has unsolved object types among the implicit arguments of the
   *  families it uses (`len nil 0.`): it is a family of rules, instantiated at every instance of its
   *  head's family ([[handover.Generics]]). `origin` is its expansion chain if it is generated (reflected,
   *  REDESIGN §6.8). */
  case RuleItem(
      name: Option[Name],
      vars: List[(Name, Tm)],
      heads: List[Tm],
      body: Option[Tm],
      span: Span,
      generic: Boolean = false,
      origin: Origin = Origin.Source
  )

  /** A query; `origin` is its expansion chain if it is generated (reflected, REDESIGN §6.8). */
  case QueryItem(vars: List[(Name, Tm)], body: Tm, span: Span, origin: Origin = Origin.Source)

  /** `τ <: a.`: closed object types. */
  case EdgeItem(sub: Tm, sup: Tm, span: Span)

  /** `%mode` about the relation `target` (closed object code), or a formula function (until C3). */
  case DirectiveItem(directive: CoreDirective, target: Option[Tm], span: Span)

  /** What a local directive returned (REDESIGN §7.1): meta code of type `decl` (closed at the top level,
   *  over the environment of a module body in one), whose attributes the handover attaches to the object
   *  constant or rule it describes ([[handover.DeclData]]). `attached` is the symbol of the declaration
   *  a prefix directive is attached to, which the result must describe. */
  case DeclItem(decl: Tm, span: Span, attached: Option[Tm] = None)

/** `%mode` (REDESIGN C3 replaces it with `%demand`); the other primitive directives are attributes of
 *  declarations ([[CoreItem.DeclItem]]). */
enum CoreDirective:
  case Mode(inputs: List[(Boolean, Option[Name], Span)])

  /** `%mode f m̄` on a formula function `f`: its body must be well-moded for the mode
   *  ([[handover.FormulaModes]]). */
  case FormulaMode(fn: Int, inputs: List[Boolean])

object CoreItem:
  /** `item` with `f` applied to its terms and `g` to the globals it names outside them. */
  def map(item: CoreItem, f: Tm => Tm, g: Int => Int): CoreItem = item match
    case GlobalItem(id) => GlobalItem(g(id))
    case r: RuleItem => r.copy(vars = r.vars.map((x, t) => (x, f(t))), heads = r.heads.map(f), body = r.body.map(f))
    case q: QueryItem => q.copy(vars = q.vars.map((x, t) => (x, f(t))), body = f(q.body))
    case e: EdgeItem => e.copy(sub = f(e.sub), sup = f(e.sup))
    case d: DirectiveItem =>
      val directive = d.directive match
        case CoreDirective.FormulaMode(fn, ins) => CoreDirective.FormulaMode(g(fn), ins)
        case other => other
      d.copy(directive = directive, target = d.target.map(f))
    case d: DeclItem => d.copy(decl = f(d.decl), attached = d.attached.map(f))

  /** The terms of an item. */
  def terms(item: CoreItem): List[Tm] = item match
    case GlobalItem(_) => Nil
    case r: RuleItem => r.vars.map(_._2) ++ r.heads ++ r.body.toList
    case q: QueryItem => q.vars.map(_._2) :+ q.body
    case e: EdgeItem => List(e.sub, e.sup)
    case d: DirectiveItem => d.target.toList
    case d: DeclItem => d.decl :: d.attached.toList
