package hugin.core
package elab

import hugin.syntax.{Tree, TreeOps}
import hugin.syntax.Trees.*

/** Object items: rules and queries, whose (uppercase) variables are bound implicitly at stage 0 with
 *  unknown object types (directives are [[Directives]]). */
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

  def elabRule(r: Rule): Unit =
    if !elabSpliceItem(r) then
      items += ruleItem(Cxt.empty, r)
      recordPart(ModulePart.Source(r))

  /** A rule in the context `base` (a module body's environment and members, or empty); `lint` is false for
   *  generated rules. */
  def ruleItem(base: Cxt, r: Rule, lint: Boolean = true): CoreItem =
    val reflected = scala.collection.mutable.Set.empty[Name]
    try reflectingVariables(reflected) {
        val start = metas.length
        val (c, vars) = bindRuleVarsFrom(base, r.heads ++ r.body.toList)
        val heads = r.heads.map(h => elabHead(c, h))
        val body = r.body.map(b => check(c, b, Val.PropT, Stage.S0))
        val generic = generalize(start) || openFamilyHead(c, heads)
        CoreItem.RuleItem(r.name.map(_.name), vars, heads, body, r.span, generic)
      }
    // a variable that reflected code uses as well is not a singleton
    finally if lint then warnSingletons(r.heads ++ r.body.toList, reflected.toSet)

  /** Whether metas created since `start` are unknown object types (implicit arguments of families that
   *  nothing determines, or the object types they were solved with): the item is then generic over them;
   *  they are allowed to stay unsolved. */
  private def generalize(start: Int): Boolean =
    val open = (start until metas.length).filter(m => metas(m).solution.isEmpty && isObjectTypeUnknown(m))
    open.foreach(allowUnsolved)
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
  def warnSingletons(trees: List[Tree], exempt: Set[Name] = Set.empty): Unit =
    val occurrences =
      TreeOps.nodes(trees).collect { case v: VarRef => v }.filterNot(v => v.name.startsWith("_") || exempt(v.name)).toList
    for (name, List(v)) <- occurrences.groupBy(_.name).toList.sortBy(_._2.head.span.start) do
      reporter.report(ElabProblem.SingletonVariable(name, v.span).toDiagnostic)

  private def elabHead(c: Cxt, h: Tree): Tm =
    state.objectHead = true
    val (tm, ty) =
      try inferS(c, h, Stage.S0)
      finally state.objectHead = false
    force(ty) match
      case Val.RelT | Val.PropT => tm
      case Val.Pi(_, _, _, _) =>
        fail(TypeProblem.IncompleteHead(h.span))
      case other if stageOfType(other) == Stage.S0 && !isUniverse(other) => tm // a constructor term: asserts the fact
      case other =>
        fail(TypeProblem.InvalidHead(show(c, other), h.span))

  def elabQuery(q: Query): Unit =
    items += queryItem(Cxt.empty, q)
    recordPart(ModulePart.Source(q))

  def queryItem(base: Cxt, q: Query): CoreItem =
    val (c, vars) = bindRuleVarsFrom(base, List(q.body))
    val body = check(c, q.body, Val.PropT, Stage.S0)
    CoreItem.QueryItem(vars, body, q.span)
