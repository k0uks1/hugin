package hugin.core
package elab

import hugin.syntax.Tree
import hugin.syntax.Trees.*
import hugin.util.*

/** Object items: rules and queries, whose (uppercase) variables are bound implicitly at stage 0 with
 *  unknown object types; directives (only their targets are resolved for now). */
trait ObjectItems:
  self: Elaborator =>
  import core.*

  /** Binds the variables of a rule or query (stage 0, of unknown object types). */
  private def bindRuleVars(trees: List[Tree]): (Cxt, List[(Name, Tm)]) =
    val vs = trees.flatMap(t => freeVars(t, Set.empty)).distinctBy(_.name)
    var c = Cxt.empty
    val out = vs.map { v =>
      val ty = freshMeta(c, Val.U0, Stage.S0, v.span, s"the type of `${v.name}`", allowUnsolved = true)
      c = bind(c, v.name, ev(c, ty), Stage.S0)
      (v.name, ty)
    }
    (c, out)

  def elabRule(r: Rule): Unit =
    val (c, vars) = bindRuleVars(r.heads ++ r.body.toList)
    val heads = r.heads.map(h => elabHead(c, h))
    val body = r.body.map(b => check(c, b, Val.PropT, Stage.S0))
    items += CoreItem.RuleItem(r.name.map(_.name), vars, heads, body, r.span)

  private def elabHead(c: Cxt, h: Tree): Tm =
    val (tm, ty) = inferS(c, h, Stage.S0)
    force(ty) match
      case Val.RelT | Val.PropT => tm
      case Val.Pi(_, _, _, _) =>
        fail(
          Diagnostic.error("E0910", "incomplete rule head", h.span, "missing arguments")
            .withNote("a rule head must apply a relation (or a constructor) to all of its columns")
        )
      case other if stageOfType(other) == Stage.S0 && !isUniverse(other) => tm // a constructor term: asserts the fact
      case other =>
        fail(
          Diagnostic.error("E0910", "invalid rule head", h.span, s"this has type `${show(c, other)}`")
            .withNote("a rule head is an atom of a relation or a constructor term")
        )

  def elabQuery(q: Query): Unit =
    val (c, vars) = bindRuleVars(List(q.body))
    val body = check(c, q.body, Val.PropT, Stage.S0)
    items += CoreItem.QueryItem(vars, body, q.span)

  def elabDirective(d: Directive): Unit =
    val target = d.args match
      case DirArgs.Mode(t, _) => Some(t)
      case DirArgs.Target(t) => Some(t)
      case DirArgs.TerminatesLabel(_, t) => Some(t)
      case DirArgs.TerminatesVar(_, t, _) => Some(t)
      case DirArgs.NameHint(t, _) => Some(t)
      case DirArgs.Infix(_, _, _) => None
    target.foreach(infer(Cxt.empty, _))
