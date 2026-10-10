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
        define(id, clauses.flatMap(cl => reporting(clause(c, 0, name, params.map(_._3), cl))))
    }

  /** Defines the formula function `name` of a module body, lifted to the global `id` ([[MemberFunctions]]),
   *  by its rules: they are elaborated in the context `cb` of the body's members, and the global is the
   *  disjunction closed over that context ([[Lifting.closeTerm]]). The definition is withheld
   *  ([[DependencyOrder.withheld]]) until the rules of all formula functions of the body are elaborated:
   *  as in a component of the top level, none unfolds in the others, and a cycle is reported before any
   *  unfolds ([[checkMemberFormulaCycles]]). */
  def elabMemberFormula(cb: Cxt, name: Name, id: Int, clauses: List[Rule]): Unit =
    val (params, result) = telescope(cb.binder(cb.scope(name)).ty, cb.lvl)
    // diagnostics name the function by its path
    val path = globals(id).name
    if force(result) == Val.Lift(Val.PropT) then
      if clauses.isEmpty then reporter.report(ElabProblem.FormulaFunctionWithoutClauses(path, globals(id).span).toDiagnostic)
      var c = cb
      for ((_, _, ty), i) <- params.zipWithIndex do c = bind(c, s"$name#${i + 1}", ty, Stage.S1)
      val alts = clauses.flatMap(cl => reporting(clause(c, cb.lvl, path, params.map(_._3), cl)))
      val tm = params.foldRight(Tm.quote(disjunction(alts)))((p, acc) => Tm.Lam(p._1, p._2, acc))
      val closed = closeTerm(cb, zonk(cb.env, cb.lvl, tm))
      withheld(id) = GlobalKind.Definition(closed, eval(Nil, closed))

  private def disjunction(alts: List[Tm]): Tm = alts match
    case List(single) => single
    case many => Tm.Obj(ObjForm.Or, many)

  /** Defines the formula function `id` as the disjunction of `alts` (false if there are none). */
  private def define(id: Int, alts: List[Tm]): Unit =
    val tm = telescope(globals(id).ty)._1.foldRight(Tm.quote(disjunction(alts)))((p, acc) => Tm.Lam(p._1, p._2, acc))
    val ztm = zonk(Nil, 0, tm)
    globals(id).kind = GlobalKind.Definition(ztm, eval(Nil, ztm))

  /** E0105: the formula functions `fns` (with their clauses, in source order) whose clauses refer to them,
   *  directly or through other definitions and functions: expanding one would not end. One error per
   *  cycle, at the first such reference; every function of the cycle is then false, and the uses of the
   *  cycle and of what refers to it are left out silently, as those of a dropped item. */
  def checkFormulaCycles(fns: List[(Name, List[Rule])]): Unit =
    val ids = fns.flatMap((n, cls) => scope.get(n).map(id => (n, id, cls)))
    val done = formulaCycles(ids, (n, id) => scope.get(n).exists(reaches(id)))
    for (n, id, _) <- ids if done(id) do state.unelaborated += n
    leaveOutUsesOf(done)

  /** E0105 for the formula functions of a module body (with their globals and rules), as
   *  [[checkFormulaCycles]], in the context `cb` of the body's members. The functions of a cycle are
   *  then false, and returned: their uses are left out ([[ElabState.leftOutMembers]]). */
  def checkMemberFormulaCycles(cb: Cxt, fns: List[(Name, Int, List[Rule])]): collection.Set[Int] =
    formulaCycles(
      fns.map((_, id, rules) => (globals(id).name, id, rules)),
      (n, id) =>
        cb.scope.get(n) match
          // a member: its value with the definitions of the body it needs
          case Some(l) => refersTo(id, closeTerm(cb, Tm.Var(cb.lvl - l - 1)), self = true)
          case None => scope.get(n).exists(reaches(id))
    )

  private def reaches(id: Int)(g: Int): Boolean = g == id || refersTo(id, Tm.Global(g), self = false)

  /** Reports a cycle among the formula functions `ids` (`uses(n, f)`: whether a name `n` of their clauses
   *  expands to a use of `f`) and defines its functions as false; the globals so defined. */
  private def formulaCycles(ids: List[(Name, Int, List[Rule])], uses: (Name, Int) => Boolean): collection.Set[Int] =
    val done = scala.collection.mutable.Set.empty[Int]
    for (name, id, cls) <- ids if !done(id) && refersTo(id, Tm.Global(id), self = false) do
      val at = cls.iterator
        .flatMap(cl => cl.body.iterator.flatMap(TreeOps.nodes))
        .collectFirst { case n: Ident if uses(n.name, id) => n.span }
      reporter.report(ElabProblem.RecursiveFormulaFunction(name, at.getOrElse(globals(id).span), globals(id).span).toDiagnostic)
      for
        (_, other, _) <- ids
        if other == id || (refersTo(id, Tm.Global(other), self = false) && refersTo(other, Tm.Global(id), self = false))
      do
        done += other
        define(other, Nil)
    done

  /** The definitions and functions of the file that expand to one of the `failed` globals: their uses are
   *  left out silently too, as those of a dropped item (reference: meta/index, "Order of elaboration"). */
  def leaveOutUsesOf(failed: collection.Set[Int]): Unit =
    for n <- state.declaredHere; g <- scope.get(n) if failed.exists(f => refersTo(f, Tm.Global(g), self = false)) do
      state.unelaborated += n

  /** Whether `t` refers to the global `target`, through the definitions and functions it refers to and the
   *  members of the module values among them; with `self = false`, `t` being `target` itself does not
   *  count (only its definition does). */
  private def refersTo(target: Int, t: Tm, self: Boolean): Boolean =
    val seen = scala.collection.mutable.Set.empty[Int]
    val seenBodies = scala.collection.mutable.Set.empty[Int]
    def inGlobal(g: Int): Boolean = kindOf(g) match
      case GlobalKind.Definition(tm, _) => inTm(tm)
      case GlobalKind.Function(_, Some(tree)) => inTree(tree)
      case _ => false
    def inTm(t: Tm): Boolean = Tm.exists(t) {
      case Tm.Global(g) => g == target || seen.add(g) && inGlobal(g)
      // a module value: the definitions of its members, whichever is selected (its member functions
      // and formula functions are globals applied to the body's context)
      case Tm.Module(b, _) =>
        seenBodies.add(b.id) && b.members.exists {
          case Member(_, MemberKind.Defined(tm), _, _, _) => inTm(tm)
          case _ => false
        }
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

  /** One clause `f t̄ :- ψ` in the context of the parameters (bound from level `base`): `fresh X̄. x̄ = t̄,
   *  ψ`. */
  private def clause(c: Cxt, base: Int, name: Name, domains: List[Val], cl: Rule): Tm =
    val head = cl.heads.head
    val args = TreeOps.flattenApp(head)._2
    if args.length != domains.length then
      fail(ElabProblem.ClauseArity(name, args.length, domains.length, head.span))
    warnSingletons(cl.heads ++ cl.body.toList)
    val (cv, vars) = bindRuleVarsFrom(c, cl.heads ++ cl.body.toList)
    val eqs = args.zip(domains).zipWithIndex.map { case ((a, dom), i) =>
      val param = Tm.loc(a.span, Tm.splice(Tm.Var(cv.lvl - base - i - 1)))
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
