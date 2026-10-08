package hugin.core

import hugin.util.*
import hugin.util.diagnostics.{Code as DiagCode, Legacy}

/** Staging: object items are evaluated by normalisation, which runs all meta code they splice
 *  (`$⟨t⟩ = t`); what remains must be pure object code. Since the meta level is total, this terminates.
 *  (As observed by Kovács, NbE of a closed object term is its staging.) */
final class Staging(core: Core, reporter: Reporter):
  import core.*

  private def stuck(span: Span, msg: String, label: String, note: String): Unit =
    reporter.report(Legacy.error(DiagCode.E0909, msg, span, label).withNote(note))

  /** Checks that a normal form is object code; reports what is not. */
  def objectCode(names: List[Name], t: Tm, span: Span): Boolean =
    var ok = true
    def bad(msg: String, label: String, note: String): Unit =
      if ok then stuck(span, msg, label, note)
      ok = false
    def go(t: Tm): Unit = t match
      case Tm.Splice(x) =>
        bad(
          "cannot compute object code at compile time",
          s"`${showTm(names, x)}` does not evaluate to object code",
          "the meta code spliced here is stuck (it applies a postulate or a variable), so no object code results"
        )
      case Tm.Persist(x) =>
        bad(
          "cannot compute a primitive value at compile time",
          s"`${showTm(names, x)}` does not evaluate to a literal",
          "a meta value used in object code must evaluate to a literal (overflow and division by zero are undefined)"
        )
      case Tm.Arith(_, a, b, Stage.S1) =>
        bad(
          "compile-time arithmetic failure",
          s"`${showTm(names, t)}` is undefined",
          "overflow and division by zero are undefined at the meta level"
        )
      case Tm.Meta(_) | Tm.AppPruning(_, _) =>
        bad("cannot infer object code", "unsolved", "an unknown in object code was not determined by elaboration")
      case Tm.App(f, a, _) => go(f); go(a)
      case Tm.Arith(_, a, b, _) => go(a); go(b)
      case Tm.Negate(a, _) => go(a)
      case Tm.Obj(_, as) => as.foreach(go)
      case Tm.Proj(a, _) => go(a)
      case Tm.Var(_) | Tm.Global(_) | Tm.Lit(_, _) => ()
      case other =>
        bad("not object code", s"`${showTm(names, other)}`", "only object terms and formulas can occur in object items")
    go(t)
    ok

  /** The leaves of a case tree as clauses, with their bodies normalised. */
  private def clauses(f: Name, tree: CaseTree): List[String] = tree match
    case CaseTree.Split(_, branches) => branches.flatMap(b => clauses(f, b.tree))
    case CaseTree.Leaf(body, _, order, names, patterns) =>
      val ns = names.toList.reverse
      val env = order.indices.reverse.map(Val.local).toList
      val pats = patterns.map(p => showArg(ns, explicitOnly(p)))
      List(s"  ${(f :: pats).mkString(" ")} = ${showTm(ns, explicitOnly(nf(env, body)))}.")

  /** The position of an item in the source: items are staged and printed in source order (elaboration
   *  may have deferred some). */
  def position(item: CoreItem): Int = item match
    case CoreItem.GlobalItem(id) => globals(id).span.start
    case r: CoreItem.RuleItem => r.span.start
    case q: CoreItem.QueryItem => q.span.start
    case e: CoreItem.EdgeItem => e.span.start
    case d: CoreItem.DirectiveItem => d.span.start

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
    case CoreItem.RuleItem(name, vars, heads, body, span) =>
      val env = vars.indices.reverse.map(Val.local).toList
      val names = vars.map(_._1).reverse
      val hs = heads.map(nf(env, _))
      val b = body.map(nf(env, _))
      if (hs ++ b.toList).forall(objectCode(names, _, span)) then
        val pre = name.map(n => s"@$n ").getOrElse("")
        List(s"$pre${hs.map(showTm(names, _)).mkString(", ")}${b.map(x => " :- " + showTm(names, x)).getOrElse("")}.")
      else Nil
    case CoreItem.QueryItem(vars, body, span) =>
      val env = vars.indices.reverse.map(Val.local).toList
      val names = vars.map(_._1).reverse
      val b = nf(env, body)
      if objectCode(names, b, span) then List(s"?- ${showTm(names, b)}.") else Nil
    case CoreItem.EdgeItem(sub, sup, _) => List(s"${showTm(Nil, nf(Nil, sub))} <: ${showTm(Nil, nf(Nil, sup))}.")
    case CoreItem.DirectiveItem(d, target, _) =>
      List((s"%${directiveName(d)}" :: target.map(t => showTm(Nil, nf(Nil, t))).toList).mkString(" ") + ".")
  }

  private def directiveName(d: CoreDirective): String = d match
    case CoreDirective.DerivationsRule(r) => s"derivations @$r"
    case CoreDirective.Mode(_) => "mode" // the target follows; modes are shown by the object level
    case CoreDirective.TerminatesLabel(_) | CoreDirective.TerminatesVar(_, _, _) => "terminates"
    case CoreDirective.NameHint(_) => "name"
    case other => other.toString.toLowerCase
