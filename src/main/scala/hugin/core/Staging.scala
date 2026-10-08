package hugin.core

import hugin.util.*

/** Staging: object items are evaluated by normalisation, which runs all meta code they splice
 *  (`$⟨t⟩ = t`); what remains must be pure object code. Since the meta level is total, this terminates.
 *  (As observed by Kovács, NbE of a closed object term is its staging.) */
final class Staging(core: Core, reporter: Reporter):
  import core.*

  private def stuck(span: Span, kind: elab.Unstaged, shown: String): Unit =
    reporter.report(elab.TypeProblem.NotStaged(kind, shown, span).toDiagnostic)

  /** Checks that a normal form is object code; reports what is not. */
  def objectCode(names: List[Name], t: Tm, span: Span): Boolean =
    var ok = true
    def bad(kind: elab.Unstaged, shown: String): Unit =
      if ok then stuck(span, kind, shown)
      ok = false
    def go(t: Tm): Unit = t match
      case Tm.Splice(x) =>
        bad(elab.Unstaged.StuckSplice, showTm(names, x))
      case Tm.Persist(x) =>
        bad(elab.Unstaged.StuckPrimitive, showTm(names, x))
      case Tm.Arith(_, a, b, Stage.S1) =>
        bad(elab.Unstaged.UndefinedArithmetic, showTm(names, t))
      case Tm.Meta(_) | Tm.AppPruning(_, _) =>
        bad(elab.Unstaged.Unsolved, "")
      case Tm.App(f, a, _) => go(f); go(a)
      case Tm.Arith(_, a, b, _) => go(a); go(b)
      case Tm.Negate(a, _) => go(a)
      case Tm.Obj(_, as) => as.foreach(go)
      case Tm.Proj(a, _) => go(a)
      case Tm.FactTy(a) => go(a) // object types in ascriptions
      case Tm.Var(_) | Tm.Global(_) | Tm.Lit(_, _) | Tm.Base(_, Stage.S0) => ()
      case other =>
        bad(elab.Unstaged.NotObjectCode, showTm(names, other))
    go(t)
    ok

  /** The leaves of a case tree as clauses, with their bodies normalised. */
  private def clauses(f: Name, tree: CaseTree): List[String] = tree match
    case CaseTree.Split(_, branches) => branches.flatMap(b => clauses(f, b.tree))
    case CaseTree.SplitAtom(_, branches, default) => branches.flatMap(b => clauses(f, b._2)) ++ clauses(f, default)
    case CaseTree.Leaf(body, _, order, names, patterns) =>
      val ns = names.toList.reverse
      val env = order.indices.reverse.map(Val.local).toList
      val pats = patterns.map(p => showArg(ns, explicitOnly(p)))
      List(s"  ${(f :: pats).mkString(" ")} = ${showTm(ns, explicitOnly(nf(env, body)))}.")

  /** The position of an item in the source: items are staged and printed in source order (elaboration
   *  may have deferred some). */
  def position(item: CoreItem): Int = item match
    case CoreItem.GlobalItem(id) => positionOf(globals(id).span)
    case r: CoreItem.RuleItem => positionOf(r.span)
    case q: CoreItem.QueryItem => positionOf(q.span)
    case e: CoreItem.EdgeItem => positionOf(e.span)
    case d: CoreItem.DirectiveItem => positionOf(d.span)
    case d: CoreItem.DeclItem => positionOf(d.span)

  /** The staged program: declarations, definitions (as elaborated, with inserted quotes, splices and
   *  implicit arguments), and object items after staging. */
  def render(items: List[CoreItem]): List[String] = items.sortBy(position).flatMap {
    case CoreItem.GlobalItem(id) =>
      val g = globals(id)
      val ty = showTm(Nil, zonk(Nil, 0, g.tyTm))
      g.kind match
        case GlobalKind.Definition(tm, _) => List(s"${g.name} : $ty = ${showTm(Nil, zonk(Nil, 0, tm))}.")
        case GlobalKind.Function(_, Some(tree)) => s"${g.name} : $ty." :: clauses(g.name, tree)
        case _ => List(s"${g.name} : $ty.")
    case CoreItem.RuleItem(name, vars, heads, body, span, generic, _) =>
      val env = vars.indices.reverse.map(Val.local).toList
      val names = vars.map(_._1).reverse
      val hs = heads.map(nf(env, _))
      val b = body.map(nf(env, _))
      // a generic rule is staged at the instances of its head's family; here it is shown with its unknowns
      if generic || (hs ++ b.toList).forall(objectCode(names, _, span)) then
        val pre = name.map(n => s"@$n ").getOrElse("")
        List(s"$pre${hs.map(showTm(names, _)).mkString(", ")}${b.map(x => " :- " + showTm(names, x)).getOrElse("")}.")
      else Nil
    case CoreItem.QueryItem(vars, body, span, _) =>
      val env = vars.indices.reverse.map(Val.local).toList
      val names = vars.map(_._1).reverse
      val b = nf(env, body)
      if objectCode(names, b, span) then List(s"?- ${showTm(names, b)}.") else Nil
    case CoreItem.EdgeItem(sub, sup, _) => List(s"${showTm(Nil, nf(Nil, sub))} <: ${showTm(Nil, nf(Nil, sup))}.")
    case CoreItem.DirectiveItem(d, target, _) =>
      val name = d match
        case CoreDirective.Mode(_) => "mode" // the target follows; modes are shown by the object level
        case CoreDirective.FormulaMode(f, _) => s"mode ${globals(f).name}"
      List((s"%$name" :: target.map(t => showTm(Nil, nf(Nil, t))).toList).mkString(" ") + ".")
    case d: CoreItem.DeclItem => declaration(d)
  }

  /** The attributes a local directive attaches, one directive each (`%input r.`). */
  private def declaration(d: CoreItem.DeclItem): List[String] =
    try
      DeclAttributes(core).decode(eval(Nil, d.decl), d.span) match
        case DeclValue.Constant(id, attrs, _) => attrs.map(a => s"${a.directive} ${globals(id).name}.")
        case DeclValue.NamedRule(n, attrs) => attrs.map(a => s"${a.directive} @$n.")
        case DeclValue.Rejected(_) => Nil
    catch case _: OpenDeclData => Nil
