package hugin.core
package elab

import hugin.obj.CmpOp
import hugin.syntax.TreeOps
import hugin.syntax.Trees.*

/** Formula functions defined by clauses (REDESIGN §6.7): `f : τ̄ -> prop.` with rules `f t̄ⱼ :- ψⱼ.` as its
 *  clauses defines `f = [x̄] ⟨(x̄ = t̄₁, ψ₁) ; … ; (x̄ = t̄ₖ, ψₖ)⟩`. The variables of a clause are local to
 *  it: they are bound by `fresh` ([[Tm.Fresh]]), so that each application gets its own (hygiene). A
 *  formula function without clauses is false (W0005). */
trait FormulaFunctions:
  self: Elaborator =>
  import core.*

  /** The names declared `f : … -> prop.` (without definition) among `items`. */
  def formulaFunctionNames(items: List[Item]): Set[Name] =
    items.collect { case d: Decl if d.defn.isEmpty && endsInProp(d.tpe) => d.name.name }.toSet

  /** The formula function a rule is a clause of. */
  def clauseOf(names: Set[Name])(item: Item): Option[Name] = item match
    case Rule(None, List(head), _) => TreeOps.headName(head).map(_.name).filter(names)
    case _ => None

  /** Defines the formula function `name` (declared, a postulate so far) by its clauses. */
  def elabFormulaClauses(name: Name, clauses: List[Rule]): Unit =
    scope.get(name).filter(id => globals(id).kind == GlobalKind.Postulate).foreach { id =>
      val g = globals(id)
      val (params, result) = telescope(g.ty)
      if force(result) == Val.Lift(Val.PropT) then
        if clauses.isEmpty then reporter.report(ObjectProblem.FormulaFunctionWithoutClauses(name, g.span).toDiagnostic)
        var c = Cxt.empty
        for (x, _, ty) <- params.zipWithIndex.map((p, i) => (s"$name#${i + 1}", p._2, p._3)) do c = bind(c, x, ty, Stage.S1)
        val alts = clauses.flatMap(cl => reporting(clause(c, name, params.map(_._3), cl)))
        val formula = alts match
          case List(single) => single
          case many => Tm.Obj(ObjForm.Or, many)
        val tm = params.foldRight(Tm.quote(formula))((p, acc) => Tm.Lam(p._1, p._2, acc))
        val ztm = zonk(Nil, 0, tm)
        g.kind = GlobalKind.Definition(ztm, eval(Nil, ztm))
    }

  private def reporting[A](a: => A): Option[A] =
    try Some(a)
    catch
      case e: ElabError =>
        reporter.report(e.diag)
        None

  /** One clause `f t̄ :- ψ` in the context of the parameters: `fresh X̄. x̄ = t̄, ψ`. */
  private def clause(c: Cxt, name: Name, domains: List[Val], cl: Rule): Tm =
    val head = cl.heads.head
    val args = TreeOps.flattenApp(head)._2
    if args.length != domains.length then
      fail(ObjectProblem.ClauseArity(name, args.length, domains.length, head.span))
    warnSingletons(cl.heads ++ cl.body.toList)
    val (cv, vars) = bindRuleVarsFrom(c, cl.heads ++ cl.body.toList)
    val eqs = args.zip(domains).zipWithIndex.map { case ((a, dom), i) =>
      val param = Tm.loc(a.span, Tm.splice(Tm.Var(cv.lvl - i - 1)))
      val arg = check(cv, a, objectType(dom), Stage.S0)
      Tm.loc(a.span, Tm.Obj(ObjForm.Compare(CmpOp.Eq), List(param, arg)))
    }
    val body = cl.body.map(check(cv, _, Val.PropT, Stage.S0)).toList
    Tm.Fresh(vars.map(_._1), Tm.Obj(ObjForm.And, eqs ++ body))

  private def objectType(dom: Val): Val = force(dom) match
    case Val.Lift(t) => t
    case other => other
