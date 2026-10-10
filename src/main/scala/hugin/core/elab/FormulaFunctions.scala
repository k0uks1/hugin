package hugin.core
package elab

import hugin.obj.CmpOp
import hugin.syntax.TreeOps
import hugin.syntax.Trees.*

/** Formula functions defined by clauses (reference: modules): `f : τ̄ -> prop.` with rules `f t̄ⱼ :- ψⱼ.` as its
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
        if clauses.isEmpty then reporter.report(ElabProblem.FormulaFunctionWithoutClauses(name, g.span).toDiagnostic)
        var c = Cxt.empty
        for (x, _, ty) <- params.zipWithIndex.map((p, i) => (s"$name#${i + 1}", p._2, p._3)) do c = bind(c, x, ty, Stage.S1)
        define(id, clauses.flatMap(cl => reporting(clause(c, name, params.map(_._3), cl))))
    }

  /** Defines the formula function `id` as the disjunction of `alts` (false if there are none). */
  private def define(id: Int, alts: List[Tm]): Unit =
    val formula = alts match
      case List(single) => single
      case many => Tm.Obj(ObjForm.Or, many)
    val tm = telescope(globals(id).ty)._1.foldRight(Tm.quote(formula))((p, acc) => Tm.Lam(p._1, p._2, acc))
    val ztm = zonk(Nil, 0, tm)
    globals(id).kind = GlobalKind.Definition(ztm, eval(Nil, ztm))

  /** E0105: the formula functions `fns` (with their clauses, in source order) whose clauses refer to them,
   *  directly or through other definitions and functions: expanding one would not end. One error per
   *  cycle, at the first such reference; every function of the cycle is then false, and the uses of the
   *  cycle and of what refers to it are left out silently, as those of a dropped item. */
  def checkFormulaCycles(fns: List[(Name, List[Rule])]): Unit =
    val ids = fns.flatMap((n, cls) => scope.get(n).map(id => (n, id, cls)))
    val done = scala.collection.mutable.Set.empty[Int]
    for (name, id, cls) <- ids if !done(id) && refersTo(id, Tm.Global(id), self = false) do
      val reaches = (g: Int) => g == id || refersTo(id, Tm.Global(g), self = false)
      val at = cls.iterator
        .flatMap(cl => cl.body.iterator.flatMap(TreeOps.nodes))
        .collectFirst { case n: Ident if scope.get(n.name).exists(reaches) => n.span }
      reporter.report(ElabProblem.RecursiveFormulaFunction(name, at.getOrElse(globals(id).span), globals(id).span).toDiagnostic)
      for
        (n, other, _) <- ids
        if other == id || (refersTo(id, Tm.Global(other), self = false) && refersTo(other, Tm.Global(id), self = false))
      do
        done += other
        state.unelaborated += n
        define(other, Nil)
    leaveOutUsesOf(done)

  /** The definitions and functions of the file that expand to one of the `failed` globals: their uses are
   *  left out silently too, as those of a dropped item (reference: meta/index, "Order of elaboration"). */
  def leaveOutUsesOf(failed: collection.Set[Int]): Unit =
    for n <- state.declaredHere; g <- scope.get(n) if failed.exists(f => refersTo(f, Tm.Global(g), self = false)) do
      state.unelaborated += n

  /** Whether `t` refers to the global `target`, through the definitions and functions it refers to; with
   *  `self = false`, `t` being `target` itself does not count (only its definition does). */
  private def refersTo(target: Int, t: Tm, self: Boolean): Boolean =
    val seen = scala.collection.mutable.Set.empty[Int]
    def inGlobal(g: Int): Boolean = kindOf(g) match
      case GlobalKind.Definition(tm, _) => inTm(tm)
      case GlobalKind.Function(_, Some(tree)) => inTree(tree)
      case _ => false
    def inTm(t: Tm): Boolean = Tm.exists(t) {
      case Tm.Global(g) => g == target || seen.add(g) && inGlobal(g)
      case _ => false
    }
    def inTree(t: CaseTree): Boolean = t match
      case CaseTree.Leaf(body, _, _, _, _) => inTm(body)
      case CaseTree.Split(_, bs) => bs.exists(b => inTree(b.tree))
      case CaseTree.SplitAtom(_, bs, d) => bs.exists((_, b) => inTree(b)) || inTree(d)
    t match
      case Tm.Global(g) if !self => seen.add(g) && inGlobal(g)
      case _ => inTm(t)

  private def reporting[A](a: => A): Option[A] =
    try Some(a)
    catch
      case e: ElabError =>
        report(e)
        None

  /** One clause `f t̄ :- ψ` in the context of the parameters: `fresh X̄. x̄ = t̄, ψ`. */
  private def clause(c: Cxt, name: Name, domains: List[Val], cl: Rule): Tm =
    val head = cl.heads.head
    val args = TreeOps.flattenApp(head)._2
    if args.length != domains.length then
      fail(ElabProblem.ClauseArity(name, args.length, domains.length, head.span))
    warnSingletons(cl.heads ++ cl.body.toList)
    val (cv, vars) = bindRuleVarsFrom(c, cl.heads ++ cl.body.toList)
    val eqs = args.zip(domains).zipWithIndex.map { case ((a, dom), i) =>
      val param = Tm.loc(a.span, Tm.splice(Tm.Var(cv.lvl - i - 1)))
      val arg = check(cv, a, objectType(dom), Stage.S0)
      Tm.loc(a.span, Tm.Obj(ObjForm.Compare(CmpOp.Eq), List(param, arg)))
    }
    val body = cl.body.map(check(cv, _, Val.PropT, Stage.S0)).toList
    val formula = Tm.Obj(ObjForm.And, eqs ++ body)
    checkObjectItem(cv, varTypes(cv, vars), Nil, List(formula))
    Tm.Fresh(vars.map(_._1), formula)

  private def objectType(dom: Val): Val = force(dom) match
    case Val.Lift(t) => t
    case other => other
