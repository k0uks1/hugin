package hugin.core
package elab

import hugin.syntax.{Tree, TreeOps}
import hugin.syntax.Trees.*
import hugin.util.*
import hugin.util.diagnostics.{Code as DiagCode, Legacy}

/** Object items: rules and queries, whose (uppercase) variables are bound implicitly at stage 0 with
 *  unknown object types, and directives. */
trait ObjectItems:
  self: Elaborator =>
  import core.*

  /** Binds the variables of object code in `c` (those not bound there already). */
  def bindRuleVarsFrom(c0: Cxt, trees: List[Tree]): (Cxt, List[(Name, Tm)]) =
    val vs = trees.flatMap(t => freeVars(t, c0.scope.keySet)).distinctBy(_.name)
    var c = c0
    val out = vs.map { v =>
      val ty = freshMeta(c, Val.U0, Stage.S0, v.span, s"the type of `${v.name}`", allowUnsolved = true)
      c = bind(c, v.name, ev(c, ty), Stage.S0)
      (v.name, ty)
    }
    (c, out)

  def elabRule(r: Rule): Unit = items += ruleItem(Cxt.empty, r)

  /** A rule in the context `base` (a module body's environment and members, or empty). */
  def ruleItem(base: Cxt, r: Rule): CoreItem =
    warnSingletons(r.heads ++ r.body.toList)
    val start = metas.length
    val (c, vars) = bindRuleVarsFrom(base, r.heads ++ r.body.toList)
    val heads = r.heads.map(h => elabHead(c, h))
    val body = r.body.map(b => check(c, b, Val.PropT, Stage.S0))
    val generic = generalize(start) || openFamilyHead(c, heads)
    CoreItem.RuleItem(r.name.map(_.name), vars, heads, body, r.span, generic)

  /** Whether metas created since `start` are unknown object types (implicit arguments of families that
   *  nothing determines, or the object types they were solved with): the item is then generic over them;
   *  they are allowed to stay unsolved. */
  private def generalize(start: Int): Boolean =
    val open = (start until metas.length).filter(m => metas(m).solution.isEmpty && isObjectTypeUnknown(m))
    open.foreach(m => metas(m).allowUnsolved = true)
    open.exists(m => force(telescope(metas(m).ty)._2) == Val.Lift(Val.U0))

  /** Whether the head of a rule is an instance of a family at unknown types (`len (cons X L) M`). */
  private def openFamilyHead(c: Cxt, heads: List[Tm]): Boolean = heads.headOption.exists { h =>
    force(Val.unloc(ev(c, h))) match
      case Val.Rigid(Head.Glob(f), sp) if globals(f).kind.isInstanceOf[GlobalKind.Family] => true
      case _ => false
  }

  private def isObjectTypeUnknown(m: Int): Boolean =
    val result = force(telescope(metas(m).ty)._2)
    result == Val.Lift(Val.U0) || result == Val.U0

  /** W0002: object variables that occur only once in a rule (names starting with `_` are exempt). */
  def warnSingletons(trees: List[Tree]): Unit =
    val occurrences = TreeOps.nodes(trees).collect { case v: VarRef => v }.filterNot(_.name.startsWith("_")).toList
    for (name, List(v)) <- occurrences.groupBy(_.name).toList.sortBy(_._2.head.span.start) do
      reporter.report(ObjectProblem.SingletonVariable(name, v.span).toDiagnostic)

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
          Legacy.error(DiagCode.E0910, "incomplete rule head", h.span, "missing arguments")
            .withNote("a rule head must apply a relation (or a constructor) to all of its columns")
        )
      case other if stageOfType(other) == Stage.S0 && !isUniverse(other) => tm // a constructor term: asserts the fact
      case other =>
        fail(
          Legacy.error(DiagCode.E0910, "invalid rule head", h.span, s"this has type `${show(c, other)}`")
            .withNote("a rule head is an atom of a relation or a constructor term")
        )

  def elabQuery(q: Query): Unit = items += queryItem(Cxt.empty, q)

  def queryItem(base: Cxt, q: Query): CoreItem =
    val (c, vars) = bindRuleVarsFrom(base, List(q.body))
    val body = check(c, q.body, Val.PropT, Stage.S0)
    CoreItem.QueryItem(vars, body, q.span)

  def elabDirective(d: Directive): Unit = items ++= directiveItem(Cxt.empty, d)

  def directiveItem(base: Cxt, d: Directive): Option[CoreItem] =
    directive(base, d).map((dir, tgt) => CoreItem.DirectiveItem(dir, tgt, d.span))

  /** A directive with its target; `None` for `%infix` (handled by the parser). */
  private def directive(base: Cxt, d: Directive): Option[(CoreDirective, Option[Tm])] =
    def target(t: Tree) = Some(relationTarget(base, t, s"%${d.kind}"))
    d.args match
      case DirArgs.Mode(Ident(n), ms) if formulaFunction(base, n).isDefined =>
        Some((CoreDirective.FormulaMode(formulaFunction(base, n).get, ms.map(_.input)), None))
      case DirArgs.Mode(t, ms) => Some((CoreDirective.Mode(ms.map(m => (m.input, m.label.map(_.name), m.span))), target(t)))
      case DirArgs.TerminatesLabel(ls, t) => Some((CoreDirective.TerminatesLabel(ls.map(_.name)), target(t)))
      case DirArgs.TerminatesVar(vs, t, args) =>
        val (c, vars) = bindRuleVarsFrom(base, args)
        Some((CoreDirective.TerminatesVar(vs.map(_.name), vars, args.map(inferS(c, _, Stage.S0)._1)), target(t)))
      case DirArgs.Target(RuleRef(rn)) => Some((CoreDirective.DerivationsRule(rn), None))
      case DirArgs.Target(t) =>
        val kind = d.kind match
          case "open" => CoreDirective.Open
          case "input" => CoreDirective.Input
          case "output" => CoreDirective.Output
          case "derivations" => CoreDirective.Derivations
          case other => fail(ObjectProblem.UnknownDirective(other, d.kindSpan))
        Some((kind, target(t)))
      case DirArgs.NameHint(t, v) => Some((CoreDirective.NameHint(v.name), target(t)))
      case DirArgs.Infix(_, _, _) => None

  /** The formula function a top-level name denotes. */
  private def formulaFunction(base: Cxt, n: Name): Option[Int] =
    if base.scope.contains(n) then None
    else scope.get(n).filter(id => globals(id).stage == Stage.S1 && force(telescope(globals(id).ty)._2) == Val.Lift(Val.PropT))

  /** The relation a directive is about: an object relation, fact constructor or struct, or meta code of a
   *  relation type. */
  private def relationTarget(base: Cxt, t: Tree, what: String): Tm =
    val (tm, ty, st) = infer(base, t)
    tm match
      case Tm.Global(id) if globals(id).kind.isInstanceOf[GlobalKind.Family] => tm // applies to each instance
      case _ => relationTargetCode(base, t, what, tm, ty, st)

  private def relationTargetCode(base: Cxt, t: Tree, what: String, tm: Tm, ty: Val, st: Stage): Tm =
    val (code, codeTy) = force(ty) match
      case Val.Lift(x) if st == Stage.S1 => (Tm.splice(tm), force(x))
      case other => (tm, other)
    dataConstructorOf(code).foreach(dataUsedAsRelation(_, t.span, s"`$what` expects a relation"))
    if !isFactConstantType(codeTy) then fail(ObjectProblem.NotARelation(what, t.span))
    zonk(base.env, base.lvl, code)
