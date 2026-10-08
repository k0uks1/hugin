package hugin.core
package elab

import hugin.syntax.{Tree, TreeOps}
import hugin.syntax.Trees.*
import hugin.util.*

/** Object items: rules and queries, whose (uppercase) variables are bound implicitly at stage 0 with
 *  unknown object types, and directives. */
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
    warnSingletons(r.heads ++ r.body.toList)
    val (c, vars) = bindRuleVars(r.heads ++ r.body.toList)
    val heads = r.heads.map(h => elabHead(c, h))
    val body = r.body.map(b => check(c, b, Val.PropT, Stage.S0))
    items += CoreItem.RuleItem(r.name.map(_.name), vars, heads, body, r.span)

  /** W0002: object variables that occur only once in a rule (names starting with `_` are exempt). */
  private def warnSingletons(trees: List[Tree]): Unit =
    val occurrences = TreeOps.nodes(trees).collect { case v: VarRef => v }.filterNot(_.name.startsWith("_")).toList
    for (name, List(v)) <- occurrences.groupBy(_.name).toList.sortBy(_._2.head.span.start) do
      reporter.report(
        Diagnostic.warning("W0002", s"variable `$name` occurs only once in this rule", v.span, "singleton variable")
          .withHelp(s"use `_` or `_$name` if this is intended")
          .withSuggestion(s"replace `$name` with `_`", v.span, "_")
          .withSuggestion(s"rename `$name` to `_$name`", v.span, s"_$name")
      )

  private def elabHead(c: Cxt, h: Tree): Tm =
    state.objectHead = true
    val (tm, ty) =
      try inferS(c, h, Stage.S0)
      finally state.objectHead = false
    dataConstructorOf(tm).foreach(dataUsedAsRelation(_, TreeOps.flattenApp(h)._1.span, "a rule head derives facts of a relation"))
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
    directive(d).foreach((dir, tgt) => items += CoreItem.DirectiveItem(dir, tgt, d.span))

  /** A directive with its target; `None` for `%infix` (handled by the parser). */
  private def directive(d: Directive): Option[(CoreDirective, Option[Tm])] =
    def target(t: Tree) = Some(relationTarget(t, s"`%${d.kind}`"))
    d.args match
      case DirArgs.Mode(t, ms) => Some((CoreDirective.Mode(ms.map(m => (m.input, m.label.map(_.name), m.span))), target(t)))
      case DirArgs.TerminatesLabel(ls, t) => Some((CoreDirective.TerminatesLabel(ls.map(_.name)), target(t)))
      case DirArgs.TerminatesVar(vs, t, args) =>
        val (c, vars) = bindRuleVars(args)
        Some((CoreDirective.TerminatesVar(vs.map(_.name), vars, args.map(inferS(c, _, Stage.S0)._1)), target(t)))
      case DirArgs.Target(RuleRef(rn)) => Some((CoreDirective.DerivationsRule(rn), None))
      case DirArgs.Target(t) =>
        val kind = d.kind match
          case "open" => CoreDirective.Open
          case "input" => CoreDirective.Input
          case "output" => CoreDirective.Output
          case "derivations" => CoreDirective.Derivations
          case other => error("E0701", s"unknown directive `%$other`", d.kindSpan)
        Some((kind, target(t)))
      case DirArgs.NameHint(t, v) => Some((CoreDirective.NameHint(v.name), target(t)))
      case DirArgs.Infix(_, _, _) => None

  /** The relation a directive is about: an object relation, fact constructor or struct, or meta code of a
   *  relation type. */
  private def relationTarget(t: Tree, what: String): Tm =
    val (tm, ty, st) = infer(Cxt.empty, t)
    val (code, codeTy) = force(ty) match
      case Val.Lift(x) if st == Stage.S1 => (Tm.splice(tm), force(x))
      case other => (tm, other)
    dataConstructorOf(code).foreach(dataUsedAsRelation(_, t.span, s"$what expects a relation"))
    if !isFactConstantType(codeTy) then error("E0701", s"$what expects a relation", t.span, "not a relation")
    zonk(Nil, 0, code)
