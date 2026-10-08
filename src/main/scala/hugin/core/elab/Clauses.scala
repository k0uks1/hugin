package hugin.core
package elab

import hugin.util.*
import scala.collection.mutable

/** Elaboration of functions defined by clauses into case trees (REDESIGN §6.4–6.5), after Cockx & Abel,
 *  *Elaborating dependent (co)pattern matching* (ICFP 2018), without copatterns:
 *
 *  A problem is a split context ([[SplitProblem]]), the target type and the clauses that may still apply,
 *  each with *equations* `term / pattern` between a term of the context and one of its patterns. Variable
 *  patterns bind, wildcards vanish, a constructor pattern against a constructor term is decomposed or
 *  rules the clause out. When the first remaining clause has no equations left, its right-hand side is
 *  checked (a leaf). Otherwise the first constructor pattern of the first clause is against a variable:
 *  the problem is split on that variable into one branch per constructor of its (inductive) type whose
 *  indices unify with the variable's type ([[IndexUnifier]]); constructors that cannot apply get no
 *  branch, so `head : vec A (suc N) -> A` needs no `vnil` clause. A branch without clauses is a missing
 *  case (coverage, E0911); a clause that never reaches a leaf is unreachable (W0006). */
trait Clauses:
  self: Elaborator =>
  import core.*

  /** An equation `term / pattern` of a clause; `ty` is the type of the term. */
  final case class Eqn(term: Val, pat: Pat, ty: Val)

  /** A clause during splitting: remaining equations and the pattern variables bound so far. */
  final case class ClauseState(index: Int, eqns: List[Eqn], binds: List[(Pat.PVar, Val, Val)], source: SurfaceClause)

  /** What the function being elaborated needs during splitting. */
  final case class FunctionInfo(
      id: Int,
      name: Name,
      arity: Int,
      explicit: List[Int],
      used: mutable.Set[Int],
      prelude: Vector[Val] => List[(Name, Val, Val)]
  )

  /** Elaborates the clauses of a declared function into its case tree. `prelude` gives the names a
   *  lifted local function sees (from the arguments at a leaf): name, type, value. */
  def elabFunction(id: Int, clauses: List[SurfaceClause], prelude: Vector[Val] => List[(Name, Val, Val)] = _ => Nil): Unit =
    val g = globals(id)
    val (binders, _) = telescope(g.ty)
    val explicitPositions = binders.zipWithIndex.collect { case ((_, Icit.Expl, _), l) => l }
    val n = clauses.head.pats.length
    clauses.find(_.pats.length != n).foreach { cl =>
      fail(ClauseProblem.PatternCount(g.name, n, cl.span))
    }
    if n > explicitPositions.length then
      fail(ClauseProblem.TooManyPatterns(g.name, explicitPositions.length, clauses.head.span))
    val arity = if n == 0 then 0 else explicitPositions(n - 1) + 1
    val (problem, target) = initialProblem(g.ty, arity)
    val info = FunctionInfo(id, g.name, arity, explicitPositions.take(n), mutable.Set.empty, prelude)
    val states = clauses.zipWithIndex.map((cl, i) => initialClause(problem, binders.take(arity), cl, i))
    val tree = buildTree(info, problem, target, states)
    g.kind = GlobalKind.Function(arity, Some(tree))
    checkTermination()
    for (cl, i) <- clauses.zipWithIndex if !info.used(i) do
      reporter.report(ClauseProblem.UnreachableClause(g.name, cl.span).toDiagnostic)

  /** The problem with the first `arity` arguments of the function as variables. */
  private def initialProblem(ty: Val, arity: Int): (SplitProblem, Val) =
    var p = SplitProblem(Vector.empty, Vector.empty, Vector.empty)
    var t = ty
    for k <- 0 until arity do
      force(t) match
        case Val.Pi(x, _, a, cl) =>
          p = p.extend(if x == "_" then s"x$k" else x, a)
          t = inst(cl, Val.local(k))
        case _ => throw Impossible("arity exceeds the function type")
    (p, t)

  private def initialClause(p: SplitProblem, binders: List[(Name, Icit, Val)], cl: SurfaceClause, index: Int): ClauseState =
    var pats = cl.pats
    val eqns = binders.zipWithIndex.map { case ((x, i, a), l) =>
      val pat =
        if i == Icit.Impl then Pat.PVar(x, cl.name.span, implicitBinder = true)
        else
          val q = pattern(pats.head)
          pats = pats.tail
          q
      Eqn(Val.local(l), pat, a)
    }
    ClauseState(index, eqns, Nil, cl)

  // ---------------------------------------------------------------- simplification of equations

  private enum Simplified:
    case NoMatch
    case Ready(cl: ClauseState)

  /** Brings a clause up to date with the problem's solutions and solves its equations as far as
   *  possible: afterwards, every equation is a constructor pattern against a free variable. */
  private def simplify(p: SplitProblem, cl: ClauseState): Simplified =
    var pending = cl.eqns.map(e => e.copy(term = p.norm(core, e.term), ty = p.norm(core, e.ty)))
    var binds = cl.binds.map((v, t, ty) => (v, p.norm(core, t), p.norm(core, ty)))
    val stuck = mutable.ListBuffer.empty[Eqn]
    var matches = true
    while matches && pending.nonEmpty do
      val e = pending.head
      pending = pending.tail
      e.pat match
        case v: Pat.PVar =>
          if !v.implicitBinder && binds.exists((b, _, _) => b.name == v.name && !b.implicitBinder) then
            fail(ClauseProblem.BoundTwice(v.name, v.span))
          binds = binds :+ (v, e.term, e.ty)
        case Pat.PWild(_) =>
        case Pat.PLit(n, span) =>
          natType(e.ty) match
            case Some((z, s)) =>
              val q = if n == 0 then Pat.PCon(z, Nil, span) else Pat.PCon(s, List(Pat.PLit(n - 1, span)), span)
              pending = e.copy(pat = q) :: pending
            case None =>
              fail(ClauseProblem.LiteralPattern(showVal(p.names.toList.reverse, e.ty), span))
        case Pat.PCon(c, args, span) =>
          force(e.term) match
            case Val.Rigid(Head.Glob(c2), sp) if isConstructor(c2) =>
              if c2 != c then matches = false
              else pending = constructorArgs(c, sp, args) ++ pending
            case Val.Rigid(Head.Local(x), Nil) if p.isFree(x) => stuck += e
            case other =>
              fail(
                ClauseProblem.CannotMatchArgument(showVal(p.names.toList.reverse, other), span)
              )
    if matches then Simplified.Ready(cl.copy(eqns = stuck.toList, binds = binds)) else Simplified.NoMatch

  /** The equations for the explicit arguments of a matched constructor. */
  private def constructorArgs(c: Int, sp: Spine, pats: List[Pat]): List[Eqn] =
    val args = sp.reverse.collect { case Elim.EApp(a, i) => (a, i) }
    var ty = globals(c).ty
    var remaining = pats
    args.flatMap { (a, i) =>
      force(ty) match
        case Val.Pi(_, _, dom, cl) =>
          ty = inst(cl, a)
          if i == Icit.Expl then
            val q = remaining.head
            remaining = remaining.tail
            Some(Eqn(a, q, dom))
          else None
        case _ => None
    }

  // ---------------------------------------------------------------- case trees

  private def buildTree(f: FunctionInfo, p: SplitProblem, target: Val, clauses: List[ClauseState]): CaseTree =
    clauses.iterator.map(simplify(p, _)).collect { case Simplified.Ready(cl) => cl }.toList match
      case Nil => absurdSplit(p).getOrElse(missingCase(f, p))
      case first :: _ if first.eqns.isEmpty => leaf(f, p, target, first)
      case all @ (first :: _) =>
        force(first.eqns.head.term) match
          case Val.Rigid(Head.Local(x), Nil) => split(f, p, x, target, all, first.eqns.head.pat)
          case _ => throw Impossible("split on a non-variable")

  /** Splits on variable `x`: a branch per constructor whose indices unify. */
  private def split(f: FunctionInfo, p: SplitProblem, x: Int, target: Val, clauses: List[ClauseState], at: Pat): CaseTree =
    val span = at match
      case Pat.PCon(_, _, s) => s
      case _ => clauses.head.source.span
    force(p.types(x)) match
      case Val.Rigid(Head.Glob(fam), famSp) if isFamily(fam) =>
        val branches = constructors(fam).flatMap { c =>
          val (p1, args, unified) = unifyConstructor(p, famSp, c)
          unified match
            case IndexUnification.Conflict => None
            case IndexUnification.Stuck(a, b) =>
              fail(
                ClauseProblem.UndecidableConstructor(
                  globals(c).name,
                  s"${showVal(p1.names.toList.reverse, a)} = ${showVal(p1.names.toList.reverse, b)}",
                  span
                )
              )
            case IndexUnification.Solved(p2) =>
              val term = args.foldLeft(Val.Rigid(Head.Glob(c), Nil): Val)((acc, a) => app(acc, p2.norm(core, a._1), a._2))
              val p3 = p2.solve(core, x, p2.norm(core, term))
              Some(CaseBranch(c, args.length, buildTree(f, p3, p3.norm(core, target), clauses)))
        }
        CaseTree.Split(x, branches)
      case other =>
        fail(ClauseProblem.NotInductive(showVal(p.names.toList.reverse, other), span))

  /** Extends the problem with the arguments of constructor `c` and unifies the indices of its type with
   *  those of the scrutinee's type `famSp`. */
  private def unifyConstructor(p: SplitProblem, famSp: Spine, c: Int): (SplitProblem, List[(Val, Icit)], IndexUnification) =
    val (p1, args) = withConstructorArgs(p, c)
    val result = args.foldLeft(globals(c).ty) { (t, a) =>
      force(t) match
        case Val.Pi(_, _, _, cl) => inst(cl, a._1)
        case other => other
    }
    val eqs = force(result) match
      case Val.Rigid(_, resSp) => resSp.reverse.zip(famSp.reverse).collect { case (Elim.EApp(a, _), Elim.EApp(b, _)) => (a, b) }
      case _ => Nil
    (p1, args, unifyIndices(p1, eqs))

  /** A free variable of an inductive type none of whose constructors can apply: the branch is
   *  impossible, an empty split covers it (`lookup vnil i` with `i : fin zero`). */
  private def absurdSplit(p: SplitProblem): Option[CaseTree] =
    (0 until p.size).filter(p.isFree).find { x =>
      force(p.types(x)) match
        case Val.Rigid(Head.Glob(fam), famSp) if isFamily(fam) =>
          constructors(fam).forall(c => unifyConstructor(p, famSp, c)._3 == IndexUnification.Conflict)
        case _ => false
    }.map(CaseTree.Split(_, Nil))

  /** Extends the problem with a variable per argument of constructor `c`. */
  private def withConstructorArgs(p: SplitProblem, c: Int): (SplitProblem, List[(Val, Icit)]) =
    var q = p
    var ty = globals(c).ty
    val args = mutable.ListBuffer.empty[(Val, Icit)]
    var more = true
    while more do
      force(ty) match
        case Val.Pi(x, i, a, cl) =>
          val v = Val.local(q.size)
          q = q.extend(if x == "_" then s"${globals(c).name}${args.length}" else x, a)
          args += ((v, i))
          ty = inst(cl, v)
        case _ => more = false
    (q, args.toList)

  /** A leaf: the first clause applies; its right-hand side is checked with its pattern variables bound. */
  private def leaf(f: FunctionInfo, p: SplitProblem, target: Val, cl: ClauseState): CaseTree =
    f.used += cl.index
    val order = p.telescopeOrder(core)
    val ren = p.renaming(core, order)
    val binds = cl.binds.map((v, value, ty) => (v, force(ren(value)), ren(ty)))
    val names = mutable.ArrayBuffer.fill(order.length)("_")
    for case (v, Val.Rigid(Head.Local(l), Nil), _) <- binds do
      if !v.implicitBinder || names(l) == "_" then names(l) = v.name
    var c = order.zipWithIndex.foldLeft(Cxt.empty) { case (cc, (l, k)) =>
      newBinder(cc, if names(k) == "_" then p.names(l) else names(k), ren(p.types(l)), Stage.S1)
    }
    val base = c.lvl
    val args = p.values.take(f.arity).map(ren)
    for (n, ty, v) <- f.prelude(args) do c = define(c, n, ty, v)
    for (v, value, ty) <- binds do
      value match
        case Val.Rigid(Head.Local(l), Nil) => c = c.copy(scope = c.scope + (v.name -> l))
        case other => c = define(c, v.name, ty, other)
    c = elabWhere(c, f.name, cl.source.where)
    val body = check(c, cl.source.rhs, ren(target), Stage.S1)
    recordCalls(f, args, c, body, cl.source)
    val patterns = f.explicit.map(l => quote(order.length, args(l)))
    CaseTree.Leaf(letBound(c, base, body), p.size, order, names.toVector, patterns)

  /** Wraps the definitions bound after level `base` around `body` as lets. */
  private def letBound(c: Cxt, base: Int, body: Tm): Tm =
    c.binders.take(c.lvl - base).foldLeft(body) { (acc, b) =>
      Tm.Let(b.name, b.tyTm, b.defn.getOrElse(throw Impossible("a pattern binder without definition")), acc)
    }

  private def missingCase(f: FunctionInfo, p: SplitProblem): Nothing =
    val names = p.names.indices.map(l => if p.isFree(l) then "_" else p.names(l)).toList.reverse
    val pats = f.explicit.map(l => showTm(names, explicitOnly(quote(p.size, p.values(l)))))
    val shown = (f.name :: pats.map(s => if s.contains(' ') then s"($s)" else s)).mkString(" ")
    fail(ClauseProblem.NotCovering(f.name, shown, globals(f.id).span))
