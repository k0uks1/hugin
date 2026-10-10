package hugin.core
package elab

import hugin.compiler.MetaIndex
import hugin.util.*
import scala.collection.mutable

/** Elaboration of functions defined by clauses into case trees (reference: meta/clauses), after Cockx & Abel,
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
      prelude: Vector[Val] => List[(Name, Val, Val)],
      /** The missing cases found so far (as the clauses' left-hand sides): coverage reports the first,
       *  tooling offers to add them all ([[MissingClauses]]). */
      missing: mutable.ListBuffer[String] = mutable.ListBuffer.empty
  )

  /** Elaborates the clauses of a declared function into its case tree. `prelude` gives the names a
   *  lifted local function sees (from the arguments at a leaf): name, type, value. */
  def elabFunction(id: Int, clauses: List[SurfaceClause], prelude: Vector[Val] => List[(Name, Val, Val)] = _ => Nil): Unit =
    val g = globals(id)
    // the clauses' names are uses of the function (for tooling)
    for cl <- clauses if cl.name.span.text == g.name do recordUse(cl.name.span, id)
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
    val tree =
      try buildTree(info, problem, target, states)
      catch case _: ElabError if info.missing.nonEmpty => notCovering(info, clauses)
    if info.missing.nonEmpty then notCovering(info, clauses)
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
    val (eqns, derived) = withDerivedBindings {
      binders.zipWithIndex.map { case ((x, i, a), l) =>
        val pat =
          if i == Icit.Impl then Pat.PVar(x, cl.name.span, implicitBinder = true)
          else
            val q = pattern(pats.head, closedType(a, l))
            pats = pats.tail
            q
        Eqn(Val.local(l), pat, a)
      }
    }
    ClauseState(index, eqns, Nil, cl.copy(where = derived ++ cl.where))

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
        case lit @ (_: Pat.PLit | _: Pat.PSucc) =>
          pending = e.copy(pat = natPattern(lit, e.ty, showVal(p.names.toList.reverse, e.ty))) :: pending
        case Pat.PAtom(key, span) =>
          force(e.term) match
            case Val.Rigid(Head.Local(x), Nil) if p.isFree(x) => stuck += e
            case other =>
              atomKey(other) match
                case Some(k) => if k != key then matches = false
                case None => fail(ClauseProblem.CannotMatchArgument(showVal(p.names.toList.reverse, other), span))
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
          case Val.Rigid(Head.Local(x), Nil) =>
            first.eqns.head.pat match
              case _: Pat.PAtom => splitAtom(f, p, x, target, all)
              case pat => split(f, p, x, target, all, pat)
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

  /** Splits on variable `x` of a type without constructors but with decidable equality: a branch per value
   *  that a clause matches it against, and a default branch for the clauses that do not. */
  private def splitAtom(f: FunctionInfo, p: SplitProblem, x: Int, target: Val, clauses: List[ClauseState]): CaseTree =
    def atomOn(e: Eqn) = e.pat.isInstanceOf[Pat.PAtom] && force(e.term) == Val.local(x)
    val keys = clauses.flatMap(_.eqns.filter(atomOn)).collect { case Eqn(_, Pat.PAtom(k, _), _) => k }.distinct
    val branches = keys.map { k =>
      val p2 = p.solve(core, x, eval(Nil, k))
      (k, buildTree(f, p2, p2.norm(core, target), clauses))
    }
    CaseTree.SplitAtom(x, branches, buildTree(f, p, target, clauses.filterNot(_.eqns.exists(atomOn))))

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

  /** Whether constructor `c` can apply to a scrutinee of type `fam famSp`, i.e. its index unification does
   *  not end in a conflict ([[unifyConstructor]]). Decided without unifying in two cases where every
   *  equation is solved by Cockx & Abel's solution rule:
   *
   *  - the result of `c`'s type is its family applied to distinct variables of its own telescope (`cons :
   *    {A} -> A -> list A -> list A`): each equation has a variable of the constructor on one side that
   *    occurs in no other equation, nor in the scrutinee's indices (they only mention earlier variables);
   *  - the scrutinee's indices are distinct free variables of the problem (`M : modes Ls`): each equation
   *    has one on one side, which occurs in no other equation and not in the constructor's side (whose
   *    variables are the constructor's own, or scrutinee variables of earlier equations).
   *
   *  Index unification renormalises the whole problem per solved equation, which made the tooling
   *  records of [[recordSplits]] a sixth of the prelude's elaboration. (Agda's coverage checker likewise
   *  treats parameters apart from indices.) */
  private def canApply(p: SplitProblem, famSp: Spine, c: Int): Boolean =
    def unified = unifyConstructor(p, famSp, c)._3 != IndexUnification.Conflict
    if !linearResult(c) && !distinctFreeVariables(p, famSp) then unified
    else
      if Clauses.crossCheck then
        Clauses.decidedWithoutUnifying.incrementAndGet()
        if !unified then Clauses.mismatches.add(globals(c).name)
      true

  /** The variables applied in `sp`, if it applies only variables (`-1` for anything else). */
  private def appliedVariables(sp: Spine, variable: Int => Boolean): List[Int] = sp.map {
    case Elim.EApp(a, _) =>
      force(a) match
        case Val.Rigid(Head.Local(l), Nil) if variable(l) => l
        case _ => -1
    case _ => -1
  }

  private def distinct(vars: List[Int]): Boolean = !vars.contains(-1) && vars.distinct.length == vars.length

  /** The result type of constructor `c` is its family applied to distinct variables of its telescope. */
  private def linearResult(c: Int): Boolean =
    val (binders, result) = telescope(globals(c).ty)
    force(result) match
      case Val.Rigid(Head.Glob(_), sp) => distinct(appliedVariables(sp, _ < binders.length))
      case _ => false

  /** The indices `famSp` of a scrutinee's type are distinct free variables of `p`. */
  private def distinctFreeVariables(p: SplitProblem, famSp: Spine): Boolean =
    distinct(appliedVariables(famSp, l => l < p.size && p.isFree(l)))

  /** A free variable of an inductive type none of whose constructors can apply: the branch is
   *  impossible, an empty split covers it (`lookup vnil i` with `i : fin zero`). */
  private def absurdSplit(p: SplitProblem): Option[CaseTree] =
    (0 until p.size).filter(p.isFree).find { x =>
      force(p.types(x)) match
        case Val.Rigid(Head.Glob(fam), famSp) if isFamily(fam) =>
          constructors(fam).forall(c => !canApply(p, famSp, c))
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
    recordSplits(p, cl)
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
    val preludeEnd = c.lvl
    for (v, value, ty) <- binds do
      val site = Option.when(!v.implicitBinder)(Site(v.span, "pattern variable"))
      value match
        case Val.Rigid(Head.Local(l), Nil) =>
          c = c.copy(scope = c.scope + (v.name -> l))
          site.foreach { s =>
            c = withSite(c, l, s)
            recordLocalDeclaration(c, l)
          }
        case other =>
          c = define(c, v.name, ty, other, site)
          recordLocalDeclaration(c, c.lvl - 1)
    val (cw, whereTerms) = elabWhere(c, f.name, cl.source.where)
    c = cw
    val body = check(c, cl.source.rhs, ren(target), Stage.S1)
    checkObjectFragments(c, body, ren(target))
    for (wc, t) <- whereTerms do recordCalls(f, args, wc, t, cl.source)
    recordCalls(f, args, c, body, cl.source)
    val patterns = f.explicit.map(l => quote(order.length, args(l)))
    CaseTree.Leaf(letBound(c, base, preludeEnd, body), p.size, order, names.toVector, patterns)

  /** The pattern variables of a clause that can be split (for tooling, [[MetaIndex.Split]]): those of an
   *  inductive type, with a pattern per constructor whose indices unify with the variable's type. */
  private def recordSplits(p: SplitProblem, cl: ClauseState): Unit = if recording then
    val fresh = FreshNames(cl.binds.map(_._1.name))
    // the explicit binders of each constructor's type, for the pattern variables of the record
    val explicitBinders = mutable.HashMap.empty[Int, List[Name]]
    for case (v, value, _) <- cl.binds if !v.implicitBinder && v.span.exists do
      force(value) match
        case Val.Rigid(Head.Local(x), Nil) if p.isFree(x) =>
          force(p.types(x)) match
            case Val.Rigid(Head.Glob(fam), famSp) if isFamily(fam) =>
              val patterns = constructors(fam).filter(c => canApply(p, famSp, c)).map { c =>
                val binders = explicitBinders.getOrElseUpdate(c, telescope(globals(c).ty)._1.collect { case (x, Icit.Expl, _) => x })
                val args = binders.map { x =>
                  fresh(if x == "_" || x.isEmpty || !x.head.isLetter then v.name else x.capitalize)
                }
                if args.isEmpty then globals(c).name else (globals(c).name :: args).mkString("(", " ", ")")
              }
              val split = MetaIndex.Split(v.span, v.name, cl.source.span, patterns)
              later(_ => index.meta.split(split))
            case _ =>
        case _ =>

  /** A case no clause covers: collected (up to a bound), so that tooling can add them all; the tree
   *  returned in its place is never used, since coverage then fails ([[notCovering]]). */
  private def missingCase(f: FunctionInfo, p: SplitProblem): CaseTree =
    val names = p.names.indices.map(l => if p.isFree(l) then "_" else p.names(l)).toList.reverse
    // the hidden arguments of a lifted function are not written by users ([[Lifting]])
    val pats = f.explicit.drop(globals(f.id).hidden).map(l => showTm(names, explicitOnly(quote(p.size, p.values(l)))))
    f.missing += (f.name :: pats.map(s => if s.contains(' ') then s"($s)" else s)).mkString(" ")
    if f.missing.length >= MaxMissing then fail(ClauseProblem.NotCovering(f.name, f.missing.head, globals(f.id).span))
    CaseTree.Split(-1, Nil)

  private val MaxMissing = 20

  /** E0911 for the first missing case; all of them are recorded for tooling (clauses with holes). */
  private def notCovering(f: FunctionInfo, clauses: List[SurfaceClause]): Nothing =
    val declared = globals(f.id).span
    if f.name.forall(ch => ch.isLetterOrDigit || ch == '_' || ch == '\'') && clauses.nonEmpty && !index.muted then
      index.meta.missing(MetaIndex.MissingClauses(declared, f.name, f.missing.toList.map(_ + " = ?."), clauses.map(_.span).maxBy(_.end)))
    fail(ClauseProblem.NotCovering(f.name, f.missing.head, declared))

object Clauses:
  /** For tests: `canApply` also unifies where it decided without unifying; `decidedWithoutUnifying` counts those
   *  decisions and `mismatches` collects the constructors where unification disagreed. */
  @volatile var crossCheck: Boolean = false
  val decidedWithoutUnifying: java.util.concurrent.atomic.AtomicLong = java.util.concurrent.atomic.AtomicLong()
  val mismatches: java.util.concurrent.ConcurrentLinkedQueue[String] = java.util.concurrent.ConcurrentLinkedQueue()
