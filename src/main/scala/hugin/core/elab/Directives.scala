package hugin.core
package elab

import hugin.syntax.{Printer, Tree}
import hugin.syntax.Trees.*
import hugin.util.*

/** What a directive may change, read from the type of its application (REDESIGN §7.1). */
enum Footprint:
  /** `decl`: the declaration of one object constant (or rule); per-item incrementality is kept. */
  case Local

  /** Items (`seq item`, `item`, `rule`, `seq rule`): added where the directive is. */
  case Additive(kind: RKind)

  /** `module -> module`: the file's rules and queries, rewritten. */
  case ModuleWide

/** Directives are meta functions (REDESIGN §7): `%d a₁ … aₙ.` resolves `d` like any name, elaborates the
 *  arguments against `d`'s parameter types (with stage inference and reification: where a `decl` is
 *  expected, a name is quoted as the declaration of its object constant), and the type of the
 *  application gives its footprint ([[Footprint]]). In the prefix form `%d a₁ … aₙ DECL`, `d a₁ … aₙ` must
 *  have type `decl -> decl` and is applied to the declaration that follows.
 *
 *  - A local directive becomes a [[CoreItem.DeclItem]]: its `decl` value, whose attributes (the primitive
 *    directives `%input`, `%terminates`, …) the handover attaches to the object constant
 *    ([[hugin.core.handover.DeclData]]). It is evaluated there, so in a module body it may refer to the
 *    body's members.
 *  - An additive directive's items are reflected and elaborated in its place, as an item `$e.`.
 *  - A module-wide directive is recorded as a part of the module ([[ModuleDirectives]]); the file's rules
 *    and queries are rewritten once all items are elaborated.
 *
 *  `%mode` (until `%demand` replaces it, C3) and `%infix` (a parse-time directive) keep their own syntax. */
trait Directives:
  self: Elaborator =>
  import core.*

  /** The items of a directive at the top level (`c` empty) or in a module body. */
  def directiveItems(c: Cxt, d: Directive, inBody: Boolean): List[CoreItem] = d.args match
    case DirArgs.Infix(_, _, _) => Nil
    case DirArgs.Mode(t, ms) => List(modeDirective(c, d, t, ms))
    case DirArgs.Apply(args, decl) =>
      val (tm, footprint, attached) = application(c, d, args, decl)
      val frame = TraceFrame(s"in expansion of `${shown(d)}`", d.span)
      footprint match
        case Footprint.Local => List(CoreItem.DeclItem(zonk(c.env, c.lvl, tm), d.span, attached.map(zonk(c.env, c.lvl, _))))
        case Footprint.Additive(k) =>
          if inBody then unsupportedAt(d.span, "directives that add items in module bodies")
          val closed = zonk(Nil, 0, tm)
          recordPart(ModulePart.Data(closed, k, frame, directive = true))
          elabReflected(closed, k, frame, d.span)
        case Footprint.ModuleWide =>
          if inBody then unsupportedAt(d.span, "module-wide directives in module bodies")
          recordPart(ModulePart.Rewrite(zonk(Nil, 0, tm), frame, d.span))
          Nil

  /** `%d a₁ … aₙ` as written. */
  def shown(d: Directive): String = d.args match
    case DirArgs.Apply(args, _) => (s"%${d.kind}" :: args.map(Printer.show)).mkString(" ")
    case _ => s"%${d.kind}"

  /** The elaborated application, its footprint and, in the prefix form, the symbol of the declaration. */
  private def application(c: Cxt, d: Directive, args: List[Tree], decl: Option[Ident]): (Tm, Footprint, Option[Tm]) =
    val n = d.kind
    if !c.scope.contains(n) && lookupGlobal(n).isEmpty then unknownDirective(c, d)
    val fn: Tree = Ident(n)(d.kindSpan)
    val app = args.foldLeft(fn)((f, a) => Apply(f, a)(f.span.to(a.span)))
    val (tm, ty, st) = insertAll(c, d.span, infer(c, app))
    def notADirective = fail(DirectiveProblem.NotADirective(shown(d), show(c, ty), d.span))
    if st != Stage.S1 then notADirective
    decl match
      case Some(name) =>
        if !isDeclTransformer(c, ty) then fail(DirectiveProblem.NotAttachable(shown(d), show(c, ty), d.span, name.span))
        val data = reify(c, name, RKind.Decl)
        (Tm.App(tm, data, Icit.Expl), Footprint.Local, Some(symbolTerm(c, name)))
      case None =>
        footprintOf(c, ty).map((tm, _, None)).getOrElse(notADirective)

  /** The footprint of a directive whose application has type `ty`. */
  private def footprintOf(c: Cxt, ty: Val): Option[Footprint] = reflectiveKind(ty) match
    case Some(RKind.Decl) => Some(Footprint.Local)
    case Some(k @ (RKind.Item | RKind.Rule | RKind.List(RKind.Item) | RKind.List(RKind.Rule))) => Some(Footprint.Additive(k))
    case _ =>
      force(ty) match
        case Val.Pi(_, Icit.Expl, dom, cl) if reflectiveKind(dom).contains(RKind.List(RKind.Item)) =>
          Option.when(reflectiveKind(inst(cl, Val.local(c.lvl))).contains(RKind.List(RKind.Item)))(Footprint.ModuleWide)
        case _ => None

  private def isDeclTransformer(c: Cxt, ty: Val): Boolean = force(ty) match
    case Val.Pi(_, Icit.Expl, dom, cl) =>
      reflectiveKind(dom).contains(RKind.Decl) && reflectiveKind(inst(cl, Val.local(c.lvl))).contains(RKind.Decl)
    case _ => false

  /** The symbol of the declaration a prefix directive is attached to (`⟨r⟩`, or meta code in a body). */
  private def symbolTerm(c: Cxt, name: Ident): Tm = symbolOf(c, name) match
    case Some(Q.SymC(id, _)) => Tm.Quote(Tm.Global(id))
    case Some(Q.SymTm(tm, _)) => tm
    case _ => fail(ReflectionProblem.NotObjectSyntax("a declaration", name.span))

  /** Whether a type is a directive's: a function whose result (after all its parameters) is a `decl` or
   *  items (`module -> module` ends in `module`). */
  def isDirectiveType(ty: Val): Boolean = directiveFootprint(ty).isDefined

  /** A global meant to be applied as a directive: not a constructor of reflective data. */
  private def isDirectiveGlobal(id: Int): Boolean =
    !globals(id).kind.isInstanceOf[GlobalKind.Constructor] && isDirectiveType(globals(id).ty)

  /** The footprint of a directive of type `ty` (applied to all its arguments), described for tooling. */
  def directiveFootprint(ty: Val): Option[String] =
    val (binders, result) = telescope(ty)
    reflectiveKind(result).collect {
      case RKind.Decl => "local: it changes a declaration"
      case RKind.List(RKind.Item)
          if binders.lastOption.exists((_, i, a) => i == Icit.Expl && reflectiveKind(a).contains(RKind.List(RKind.Item))) =>
        "module-wide: it rewrites the module"
      case RKind.Item | RKind.Rule | RKind.List(RKind.Item) | RKind.List(RKind.Rule) => "additive: it adds items"
    }

  /** E0101, with a directive in scope of a similar name. */
  private def unknownDirective(c: Cxt, d: Directive): Nothing =
    val globalNames =
      (scope.keys ++ file.parent.keys).toList.distinct.filter(n => lookupGlobal(n).exists(isDirectiveGlobal))
    // a later declaration may declare it (the items of module bodies are elaborated with the declarations)
    throw ElabError(DirectiveProblem.UnknownDirective(d.kind, d.kindSpan, similarName(d.kind, globalNames)).toDiagnostic, Some(d.kind))

  // ---------------------------------------------------------------- %mode (until C3)

  private def modeDirective(c: Cxt, d: Directive, t: Tree, ms: List[ModeItem]): CoreItem = t match
    case Ident(n) if formulaFunction(c, n).isDefined =>
      CoreItem.DirectiveItem(CoreDirective.FormulaMode(formulaFunction(c, n).get, ms.map(_.input)), None, d.span)
    case _ =>
      val inputs = ms.map(m => (m.input, m.label.map(_.name), m.span))
      CoreItem.DirectiveItem(CoreDirective.Mode(inputs), Some(relationTarget(c, t, "%mode")), d.span)

  /** The formula function a top-level name denotes. */
  private def formulaFunction(c: Cxt, n: Name): Option[Int] =
    if c.scope.contains(n) then None
    else scope.get(n).filter(id => globals(id).stage == Stage.S1 && force(telescope(globals(id).ty)._2) == Val.Lift(Val.PropT))

  /** The relation `%mode` is about: an object relation, fact constructor or struct, a family of them, or
   *  meta code of a relation type. */
  private def relationTarget(c: Cxt, t: Tree, what: String): Tm =
    val (tm, ty, st) = infer(c, t)
    tm match
      case Tm.Global(id) if globals(id).kind.isInstanceOf[GlobalKind.Family] => tm // applies to each instance
      case _ =>
        val (code, codeTy) = force(ty) match
          case Val.Lift(x) if st == Stage.S1 => (Tm.splice(tm), force(x))
          case other => (tm, other)
        dataConstructorOf(code).foreach(dataUsedAsRelation(_, t.span, s"`$what` expects a relation"))
        if !isFactConstantType(codeTy) then fail(DirectiveProblem.NotARelation(what, t.span))
        zonk(c.env, c.lvl, code)
