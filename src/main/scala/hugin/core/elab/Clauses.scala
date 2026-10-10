package hugin.core
package elab

import hugin.compiler.MetaIndex
import hugin.syntax.{Tree, TreeOps}
import hugin.syntax.Trees.{Absent, Parens}
import hugin.util.*
import hugin.util.diagnostics.{Applicability, Edit, Suggestion}
import scala.collection.mutable

/** Elaboration of functions defined by clauses into case trees (reference: meta/clauses), after Cockx & Abel,
 *  *Elaborating dependent (co)pattern matching* (ICFP 2018), without copatterns:
 *
 *  A problem is a split context ([[SplitProblem]]), the target type and the clauses that may still apply,
 *  each with *equations* `term / pattern` between a term of the context and one of its patterns. Variable
 *  patterns bind, wildcards vanish, a constructor pattern against a constructor term is decomposed or
 *  rules the clause out. When the first remaining clause has no equations left, it is the leaf.
 *  Otherwise the first constructor pattern of the first clause is against a variable: the problem is
 *  split on that variable into one branch per constructor of its (inductive) type whose indices unify
 *  with the variable's type ([[IndexUnifier]]); constructors that cannot apply get no branch, so `head :
 *  vec A (suc N) -> A` needs no `vnil` clause. A branch without clauses is a missing case (coverage,
 *  E0911); a clause that never reaches a leaf is unreachable (W0006).
 *
 *  Each clause is first checked on its own, as Agda, Idris 2 and Lean 4 do: its *clause context* is the
 *  single leaf of the problem split by that clause alone (its left-hand side). A clause whose own
 *  constructors cannot occur there is an error (E0915), as is an absurd pattern `()` at a position that
 *  is not empty. The right-hand side, the `where` block and the calls for the termination check are
 *  elaborated once, in the clause context; a leaf of the case tree instantiates the clause context in the
 *  leaf's case by matching ([[CaseTree.Leaf]]). */
trait Clauses:
  self: Elaborator =>
  import core.*

  /** An equation `term / pattern` of a clause; `ty` is the type of the term. */
  final case class Eqn(term: Val, pat: Pat, ty: Val)

  /** A clause during splitting: remaining equations and the pattern variables bound so far. */
  final case class ClauseState(index: Int, eqns: List[Eqn], binds: List[(Pat.PVar, Val, Val)], source: SurfaceClause):
    /** An absurd clause `f p̄.` (with `()` in its patterns): it has no right-hand side and matches nothing. */
    def absurd: Boolean = source.rhs.isInstanceOf[Absent]

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
      missing: mutable.ListBuffer[String] = mutable.ListBuffer.empty,
      /** The leaves found so far, per clause: its case and its state there. */
      leaves: mutable.HashMap[Int, mutable.ListBuffer[(SplitProblem, ClauseState)]] = mutable.HashMap.empty
  )

  /** A clause checked in its clause context `ctx` (whose free variables, in the telescope order `order`,
   *  are the variables of the right-hand side): its body and display, and what the termination check needs
   *  to record its calls again at an instance of the context ([[alternativeCalls]]). */
  private final case class Checked(
      ctx: SplitProblem,
      order: Vector[Int],
      state: ClauseState,
      display: ClauseBody,
      rhs: Option[CheckedRhs]
  )

  /** The elaborated right-hand side `body` in context `c`, the terms of its `where` block, and whether
   *  they record calls. */
  private final case class CheckedRhs(c: Cxt, body: Tm, whereTerms: List[(Cxt, Tm)], calls: Boolean)

  /** Elaborates the clauses of a declared function into its case tree. `prelude` gives the names a
   *  lifted local function sees (from its arguments in a clause context): name, type, value. */
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
    // each clause in its own context: its left-hand side, then its right-hand side
    val contexts = states.map(cl => clauseContext(problem, target, cl, states.length == 1))
    val checked = contexts.map { (p, t, cl) =>
      try checkClause(info, p, t, cl, speculative = false)
      catch case e: ElabError if !e.silent => throw withRefinementFix(e, info, problem, target, states, cl)
    }.toVector
    val tree =
      try buildTree(info, problem, target, states, leaf(info, checked))
      catch case _: ElabError if info.missing.nonEmpty => notCovering(info, clauses)
    if info.missing.nonEmpty then notCovering(info, clauses)
    val body = FunctionBody(tree, checked.map(_.display))
    // a function of the cycle being elaborated gets its case tree when the cycle is done ([[DependencyOrder]])
    if g.inCycle then
      g.kind = GlobalKind.Function(arity, None)
      withheld(id) = GlobalKind.Function(arity, Some(body))
    else g.kind = GlobalKind.Function(arity, Some(body))
    for ch <- checked do alternativeCalls(info, ch)
    checkTermination()
    for (cl, i) <- clauses.zipWithIndex if !info.used(i) && !states(i).absurd do
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
    // `()` only in an absurd clause, which has no right-hand side
    if !cl.rhs.isInstanceOf[Absent] && cl.pats.exists(TreeOps.hasAbsurd) then
      fail(ClauseProblem.AbsurdWithRhs(Span(cl.rhs.span.origin, cl.pats.last.span.until, cl.rhs.span.until), cl.rhs.span))
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

  // ---------------------------------------------------------------- clause contexts

  private def isAbsurd(p: Pat): Boolean = p.isInstanceOf[Pat.PAbsurd]

  /** The clause context of `cl`: the problem split by `cl` alone, with `cl`'s state at its single leaf
   *  (its equations left are its absurd patterns, each against a variable of an empty type). E0915 if a
   *  constructor of the clause cannot occur (`only`: the clause is the function's only one). */
  @scala.annotation.tailrec
  private def clauseContext(p: SplitProblem, target: Val, cl: ClauseState, only: Boolean): (SplitProblem, Val, ClauseState) =
    simplify(p, cl) match
      case Simplified.NoMatch(Pat.PAbsurd(span), term) =>
        fail(ClauseProblem.AbsurdNotEmpty(wild(p, p.norm(core, typeAt(p, cl, span))), List(headName(term)), span))
      case Simplified.NoMatch(pat, term) =>
        fail(impossible(p, cl, pat, ClauseConflict.Argument(wild(p, term)), only))
      case Simplified.Ready(c) =>
        c.eqns.find(e => !isAbsurd(e.pat)) match
          case None =>
            c.eqns.foreach(checkAbsurd(p, _))
            (p, target, c)
          case Some(e) =>
            val x = force(e.term) match
              case Val.Rigid(Head.Local(x), Nil) => x
              case _ => throw Impossible("split on a non-variable")
            e.pat match
              case Pat.PAtom(k, _) =>
                val p2 = p.solve(core, x, eval(Nil, k))
                clauseContext(p2, p2.norm(core, target), c, only)
              case pat @ Pat.PCon(ctor, _, span) =>
                force(p.types(x)) match
                  case Val.Rigid(Head.Glob(fam), famSp) if isFamily(fam) =>
                    if !constructors(fam).contains(ctor) then
                      fail(impossible(p, c, pat, ClauseConflict.Family(wild(p, p.types(x))), only))
                    val (p1, args, unified) = unifyConstructor(p, famSp, ctor)
                    unified match
                      case IndexUnification.Conflict(a, b) =>
                        fail(impossible(p, c, pat, ClauseConflict.Index(wild(p1, a), wild(p1, b)), only))
                      case IndexUnification.Stuck(a, b) =>
                        fail(undecidable(p1, ctor, a, b, span))
                      case IndexUnification.Solved(p2) =>
                        val p3 = p2.solve(core, x, p2.norm(core, constructorApp(p2, ctor, args)))
                        clauseContext(p3, p3.norm(core, target), c, only)
                  case other => fail(ClauseProblem.NotInductive(showVal(p.names.toList.reverse, other), span))
              case _ => throw Impossible("a stuck equation that is not a constructor pattern")

  /** `c` applied to its arguments, values of `p`. */
  private def constructorApp(p: SplitProblem, c: Int, args: List[(Val, Icit)]): Val =
    args.foldLeft(Val.Rigid(Head.Glob(c), Nil): Val)((acc, a) => app(acc, p.norm(core, a._1), a._2))

  /** The type of the equation of `cl` whose pattern is at `span` (for a diagnostic). */
  private def typeAt(p: SplitProblem, cl: ClauseState, span: Span): Val =
    cl.eqns.find(_.pat match
      case Pat.PAbsurd(s) => s == span
      case _ => false
    ).map(_.ty).getOrElse(Val.Wild)

  /** The name of the constructor a value is an application of (for a diagnostic). */
  private def headName(v: Val): String = force(v) match
    case Val.Rigid(Head.Glob(c), _) => globals(c).name
    case other => showVal(Nil, other)

  /** A value of `p` as shown in a diagnostic: its free variables as `_`. */
  private def wild(p: SplitProblem, v: Val): String =
    val names = p.names.indices.map(l => if p.isFree(l) then "_" else p.names(l)).toList.reverse
    showTm(names, explicitOnly(quote(p.size, v)))

  /** An absurd pattern's variable must have a type none of whose constructors can occur (E0915 otherwise). */
  private def checkAbsurd(p: SplitProblem, e: Eqn): Unit =
    val span = e.pat match
      case Pat.PAbsurd(s) => s
      case _ => Span.NoSpan
    force(e.term) match
      case Val.Rigid(Head.Local(x), Nil) if p.isFree(x) =>
        force(p.types(x)) match
          case Val.Rigid(Head.Glob(fam), famSp) if isFamily(fam) =>
            val possible = constructors(fam).filter { c =>
              val (p1, _, unified) = unifyConstructor(p, famSp, c)
              unified match
                case _: IndexUnification.Conflict => false
                case IndexUnification.Stuck(a, b) => fail(undecidable(p1, c, a, b, span))
                case _: IndexUnification.Solved => true
            }
            if possible.nonEmpty then fail(ClauseProblem.AbsurdNotEmpty(wild(p, p.types(x)), possible.map(globals(_).name), span))
          case other => fail(ClauseProblem.NotInductive(showVal(p.names.toList.reverse, other), span))
      case other => fail(ClauseProblem.AbsurdNotEmpty(wild(p, e.ty), List(headName(other)), span))

  private def undecidable(p: SplitProblem, c: Int, a: Val, b: Val, span: Span): ClauseProblem =
    ClauseProblem.UndecidableConstructor(
      globals(c).name,
      s"${showVal(p.names.toList.reverse, a)} = ${showVal(p.names.toList.reverse, b)}",
      span
    )

  /** E0915 for a constructor pattern of `cl` that cannot occur in its own context, with a fix that removes
   *  the clause or, for the function's only clause, makes the pattern absurd if no constructor can occur
   *  there. */
  private def impossible(p: SplitProblem, cl: ClauseState, pat: Pat, why: ClauseConflict, only: Boolean): ClauseProblem =
    val (ctor, span) = pat match
      case Pat.PCon(c, _, s) => (globals(c).name, s)
      case Pat.PAtom(k, s) => (showTm(Nil, k), s)
      case other => ("", Span.NoSpan)
    val source = cl.source
    val written = patternTree(source, span).map(_.span).getOrElse(span)
    val absurd =
      if !only || source.where.nonEmpty || !source.rhs.span.exists || !written.exists then None
      else
        // the variable the pattern is against, if no constructor of its type can occur
        cl.eqns.find(_.pat == pat).map(e => force(e.term)).collect {
          case Val.Rigid(Head.Local(x), Nil) if p.isFree(x) => x
        }.filter { x =>
          force(p.types(x)) match
            case Val.Rigid(Head.Glob(fam), famSp) if isFamily(fam) =>
              constructors(fam).forall(c => unifyConstructor(p, famSp, c)._3.isInstanceOf[IndexUnification.Conflict])
            case _ => false
        }.map(_ => (written, Span(source.rhs.span.origin, source.pats.last.span.until, source.rhs.span.until)))
    val removal = Option.when(!only)(wholeLines(source.span))
    ClauseProblem.ImpossibleClause(ctor, why, span, removal, absurd)

  /** The surface pattern of `cl` at `span`, with its parentheses. */
  private def patternTree(cl: SurfaceClause, span: Span): Option[Tree] =
    TreeOps.nodes(cl.pats).collectFirst {
      case t @ Parens(inner) if inner.span == span => t
    }.orElse(TreeOps.nodes(cl.pats).collectFirst { case t: Tree if t.span == span => t })

  /** `span` with the whitespace before it on its first line and the line break after it, if it is alone on
   *  its lines: what removing an item removes. */
  private def wholeLines(span: Span): Span =
    if !span.exists then span
    else
      val text = span.origin.content
      var from = span.from
      while from > 0 && (text(from - 1) == ' ' || text(from - 1) == '\t') do from -= 1
      var until = span.until
      while until < text.length && (text(until) == ' ' || text(until) == '\t') do until += 1
      val startsLine = from == 0 || text(from - 1) == '\n'
      val endsLine = until >= text.length || text(until) == '\n'
      if startsLine && endsLine then Span(span.origin, from, (until + 1).min(text.length)) else span

  // ---------------------------------------------------------------- simplification of equations

  private enum Simplified:
    /** The clause does not apply: its pattern `pat` against `term`, a constructor application. */
    case NoMatch(pat: Pat, term: Val)
    case Ready(cl: ClauseState)

  /** Brings a clause up to date with the problem's solutions and solves its equations as far as
   *  possible: afterwards, every equation is a constructor pattern against a free variable. */
  private def simplify(p: SplitProblem, cl: ClauseState): Simplified =
    var pending = cl.eqns.map(e => e.copy(term = p.norm(core, e.term), ty = p.norm(core, e.ty)))
    var binds = cl.binds.map((v, t, ty) => (v, p.norm(core, t), p.norm(core, ty)))
    val stuck = mutable.ListBuffer.empty[Eqn]
    var clash: Simplified.NoMatch | Null = null
    def matches = clash == null
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
        case Pat.PAtom(key, span) =>
          force(e.term) match
            case Val.Rigid(Head.Local(x), Nil) if p.isFree(x) => stuck += e
            case other =>
              atomKey(other) match
                case Some(k) => if k != key then clash = Simplified.NoMatch(e.pat, other)
                case None => fail(ClauseProblem.CannotMatchArgument(showVal(p.names.toList.reverse, other), span))
        case Pat.PCon(c, args, span) =>
          force(e.term) match
            case term @ Val.Rigid(Head.Glob(c2), sp) if isConstructor(c2) =>
              if c2 != c then clash = Simplified.NoMatch(e.pat, term)
              else pending = constructorArgs(c, sp, args) ++ pending
            case Val.Rigid(Head.Local(x), Nil) if p.isFree(x) => stuck += e
            case other =>
              fail(
                ClauseProblem.CannotMatchArgument(showVal(p.names.toList.reverse, other), span)
              )
        case Pat.PAbsurd(_) =>
          force(e.term) match
            case Val.Rigid(Head.Local(x), Nil) if p.isFree(x) => stuck += e
            // a constructor where the clause has `()`
            case other => clash = Simplified.NoMatch(e.pat, other)
    if matches then Simplified.Ready(cl.copy(eqns = stuck.toList, binds = binds)) else clash.nn

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

  /** Builds the leaf of a clause in a case of the tree. */
  private type LeafBuilder = (SplitProblem, ClauseState) => CaseTree

  private def buildTree(f: FunctionInfo, p: SplitProblem, target: Val, clauses: List[ClauseState], leaf: LeafBuilder): CaseTree =
    clauses.iterator.map(simplify(p, _)).collect { case Simplified.Ready(cl) => cl }.toList match
      case Nil => absurdSplit(p).getOrElse(missingCase(f, p))
      case first :: _ if first.eqns.isEmpty =>
        f.used += first.index
        f.leaves.getOrElseUpdate(first.index, mutable.ListBuffer.empty) += ((p, first))
        leaf(p, first)
      case all @ (first :: _) =>
        // an absurd pattern splits only when the clause has no other constructor pattern left
        val e = first.eqns.find(e => !isAbsurd(e.pat)).getOrElse(first.eqns.head)
        force(e.term) match
          case Val.Rigid(Head.Local(x), Nil) =>
            e.pat match
              case _: Pat.PAtom => splitAtom(f, p, x, target, all, leaf)
              case pat => split(f, p, x, target, all, pat, leaf)
          case _ => throw Impossible("split on a non-variable")

  /** Splits on variable `x`: a branch per constructor whose indices unify. */
  private def split(f: FunctionInfo, p: SplitProblem, x: Int, target: Val, clauses: List[ClauseState], at: Pat, leaf: LeafBuilder): CaseTree =
    val span = at match
      case Pat.PCon(_, _, s) => s
      case Pat.PAbsurd(s) => s
      case _ => clauses.head.source.span
    force(p.types(x)) match
      case Val.Rigid(Head.Glob(fam), famSp) if isFamily(fam) =>
        val branches = constructors(fam).flatMap { c =>
          val (p1, args, unified) = unifyConstructor(p, famSp, c)
          unified match
            case _: IndexUnification.Conflict => None
            case IndexUnification.Stuck(a, b) => fail(undecidable(p1, c, a, b, span))
            case IndexUnification.Solved(p2) =>
              val p3 = p2.solve(core, x, p2.norm(core, constructorApp(p2, c, args)))
              Some(CaseBranch(c, args.length, buildTree(f, p3, p3.norm(core, target), clauses, leaf)))
        }
        CaseTree.Split(x, branches)
      case other =>
        fail(ClauseProblem.NotInductive(showVal(p.names.toList.reverse, other), span))

  /** Splits on variable `x` of a type without constructors but with decidable equality: a branch per value
   *  that a clause matches it against, and a default branch for the clauses that do not. */
  private def splitAtom(f: FunctionInfo, p: SplitProblem, x: Int, target: Val, clauses: List[ClauseState], leaf: LeafBuilder): CaseTree =
    def atomOn(e: Eqn) = e.pat.isInstanceOf[Pat.PAtom] && force(e.term) == Val.local(x)
    val keys = clauses.flatMap(_.eqns.filter(atomOn)).collect { case Eqn(_, Pat.PAtom(k, _), _) => k }.distinct
    val branches = keys.map { k =>
      val p2 = p.solve(core, x, eval(Nil, k))
      (k, buildTree(f, p2, p2.norm(core, target), clauses, leaf))
    }
    CaseTree.SplitAtom(x, branches, buildTree(f, p, target, clauses.filterNot(_.eqns.exists(atomOn)), leaf))

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
    def unified = !unifyConstructor(p, famSp, c)._3.isInstanceOf[IndexUnification.Conflict]
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

  /** Checks clause `cl` in its clause context `p` (or, `speculative`, at a leaf of the case tree, for
   *  [[withRefinementFix]]: without records): its right-hand side and `where` block with its pattern
   *  variables bound, and the calls for the termination check. */
  private def checkClause(f: FunctionInfo, p: SplitProblem, target: Val, cl: ClauseState, speculative: Boolean): Checked =
    if !speculative then recordSplits(p, cl)
    val order = p.telescopeOrder(core)
    val ren = p.renaming(core, order)
    val binds = cl.binds.map((v, value, ty) => (v, force(ren(value)), ren(ty)))
    val names = mutable.ArrayBuffer.fill(order.length)("_")
    for case (v, Val.Rigid(Head.Local(l), Nil), _) <- binds do
      if !v.implicitBinder || names(l) == "_" then names(l) = v.name
    val args = p.values.take(f.arity).map(ren)
    val patterns = f.explicit.map(l => quote(order.length, args(l)))
    if cl.absurd then
      // the variables of the absurd patterns are shown as `()`
      for e <- cl.eqns do
        force(ren(e.term)) match
          case Val.Rigid(Head.Local(l), Nil) => names(l) = "()"
          case _ =>
      Checked(p, order, cl, ClauseBody(None, names.toVector, patterns), None)
    else
      var c = order.zipWithIndex.foldLeft(Cxt.empty) { case (cc, (l, k)) =>
        newBinder(cc, if names(k) == "_" then p.names(l) else names(k), ren(p.types(l)), Stage.S1)
      }
      val base = c.lvl
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
      val before = callCount
      if !speculative then
        for (wc, t) <- whereTerms do recordCalls(f, args, wc, t, cl.source, cl.index)
        recordCalls(f, args, c, body, cl.source, cl.index)
      val display = ClauseBody(Some(letBound(c, base, preludeEnd, body)), names.toVector, patterns)
      Checked(p, order, cl, display, Some(CheckedRhs(c, body, whereTerms, callCount > before)))

  /** The leaves of the case tree: clause `cl`'s right-hand side at the instance of its clause context in
   *  the leaf's case `p`. */
  private def leaf(f: FunctionInfo, checked: Vector[Checked]): LeafBuilder = (p, cl) =>
    val ch = checked(cl.index)
    val sub = instantiation(f.arity, ch.ctx, p)
    val subst = ch.order.map(l => quote(p.size, sub(l)))
    CaseTree.Leaf(ch.display.body.getOrElse(throw Impossible("a leaf of an absurd clause")), p.size, subst, cl.index)

  /** The matching substitution from a clause context `ctx` to a case `p` of the tree that is an instance
   *  of it: a value of `p` for each free variable of `ctx`, found by matching the first `arity` arguments
   *  (every free variable of a clause context occurs in them). */
  private def instantiation(arity: Int, ctx: SplitProblem, p: SplitProblem): Map[Int, Val] =
    val sub = mutable.HashMap.empty[Int, Val]
    def go(a: Val, b: Val): Unit = force(a) match
      case Val.Rigid(Head.Local(x), Nil) if ctx.isFree(x) => if !sub.contains(x) then sub(x) = b
      case Val.Rigid(Head.Glob(c), sp) if isConstructor(c) =>
        force(b) match
          case Val.Rigid(Head.Glob(c2), sp2) if c2 == c && sp.length == sp2.length =>
            sp.zip(sp2).foreach {
              case (Elim.EApp(x, _), Elim.EApp(y, _)) => go(x, y)
              case _ =>
            }
          case _ =>
      case _ =>
    for l <- 0 until arity do go(ctx.values(l), p.values(l))
    (0 until ctx.size).filter(ctx.isFree).foreach { x =>
      if !sub.contains(x) then throw Impossible(s"the clause variable `${ctx.names(x)}` is not matched at a leaf")
    }
    sub.toMap

  /** Whether `sub` renames the free variables of `ctx` (in `order`) to those of `p`: the leaf's case is
   *  the clause context itself. */
  private def isRenaming(sub: Map[Int, Val], order: Vector[Int], p: SplitProblem): Boolean =
    val targets = order.map(l => force(sub(l)) match
      case Val.Rigid(Head.Local(y), Nil) if p.isFree(y) => y
      case _ => -1
    )
    !targets.contains(-1) && targets.distinct.length == targets.length && targets.length == (0 until p.size).count(p.isFree)

  /** For a clause with calls whose leaves refine its clause context: its calls at its leaves, which the
   *  termination check uses for a fix that writes out the clause's cases ([[SizeChange]]). */
  private def alternativeCalls(f: FunctionInfo, ch: Checked): Unit = ch.rhs match
    case Some(rhs) if rhs.calls =>
      val leaves = f.leaves.get(ch.state.index).map(_.toList).getOrElse(Nil)
      val subs = leaves.map((p, _) => (p, instantiation(f.arity, ch.ctx, p)))
      val exact = subs match
        case List((p, sub)) => isRenaming(sub, ch.order, p)
        case _ => false
      if !exact && leaves.nonEmpty then
        refinedClause(f, ch.state, leaves).foreach { text =>
          val n = ch.order.length
          val visits = subs.flatMap { (p, sub) =>
            val env = instantiatedEnv(rhs.c, n, ch.order.map(sub))
            val args = p.values.take(f.arity)
            def at(c: Cxt, t: Tm) = (args, c, env.take(c.lvl).reverse.toList, p.size + c.lvl - n, t)
            rhs.whereTerms.map(at) :+ at(rhs.c, rhs.body)
          }
          recordAlternative(f, ch.state.index, visits, ch.state.source, text)
        }
    case _ =>

  /** The values of the levels of `c` (in level order) with its first `n` (the clause context's variables)
   *  replaced by `sigma`: the definitions after them are evaluated again. */
  private def instantiatedEnv(c: Cxt, n: Int, sigma: Vector[Val]): Vector[Val] =
    val old = c.env.reverse.toVector
    val out = mutable.ArrayBuffer.empty[Val]
    for l <- 0 until c.lvl do
      out += (
        if l < n then sigma(l)
        else
          c.binder(l).defn match
            case Some(d) => eval(out.reverseIterator.toList, d)
            case None => old(l)
      )
    out.toVector

  /** A right-hand side that fails in its clause context may check at the clause's leaves of the case tree
   *  (it relies on the refinement made by earlier clauses): the error then gets a fix that writes out
   *  those cases ([[refinedClause]]). */
  private def withRefinementFix(e: ElabError, f: FunctionInfo, problem: SplitProblem, target: Val, states: List[ClauseState], cl: ClauseState): ElabError =
    if cl.source.where.nonEmpty || cl.absurd then e
    else
      val probe = f.copy(used = mutable.Set.empty, missing = mutable.ListBuffer.empty, leaves = mutable.HashMap.empty)
      val built =
        try
          buildTree(probe, problem, target, states, (_, _) => CaseTree.Split(-1, Nil))
          true
        catch case _: ElabError => false
      val leaves = probe.leaves.get(cl.index).map(_.toList).getOrElse(Nil)
      def checksAt(p: SplitProblem, lcl: ClauseState): Boolean =
        val saved = index.muted
        val mark = reporter.mark
        index.muted = true
        try tentatively { checkClause(f, p, p.norm(core, target), lcl, speculative = true); true }
        catch case _: ElabError => false
        finally
          index.muted = saved
          reporter.discardSince(mark)
      if !built || leaves.isEmpty || !leaves.forall(checksAt) then e
      else
        refinedClause(f, cl, leaves) match
          case Some(text) =>
            val fix = Suggestion(
              s"write out the cases of this clause: `${text.linesIterator.map(_.trim).mkString(" ")}`",
              List(Edit(cl.source.span, text)),
              Applicability.MachineApplicable
            )
            ElabError(e.diag.copy(suggestions = e.diag.suggestions :+ fix), e.unresolved, e.silent)
          case None => e

  /** The text of clause `cl` written out at its leaves `leaves`: one clause per leaf, with the patterns of
   *  the leaf's case. A pattern variable that the leaf refines to a constructor term is replaced by that
   *  term in the right-hand side. `None` where this is not possible as text: quoted patterns, a refined
   *  variable used in a `where` block or bound again by a lambda, or a variable of the term that only an
   *  implicit argument would bind. */
  private def refinedClause(f: FunctionInfo, cl: ClauseState, leaves: List[(SplitProblem, ClauseState)]): Option[String] =
    val source = cl.source
    val hidden = globals(f.id).hidden
    val written = source.pats.drop(hidden)
    if !source.span.exists || written.exists(t => !t.span.exists || TreeOps.nodes(t).exists(_.isInstanceOf[hugin.syntax.Trees.Quote])) then None
    else
      val origin = source.span.origin
      val lhsEnd = written.lastOption.map(_.span.until).getOrElse(source.name.span.until)
      val inRest = (sp: Span) => sp.exists && (sp.origin eq origin) && sp.from >= lhsEnd && sp.until <= source.span.until
      val uses = TreeOps.nodes((source.rhs, source.where)).collect { case v: hugin.syntax.Trees.VarRef if inRest(v.span) => v }.toList
      val lambdaBound = TreeOps.nodes(source.rhs).collect { case l: hugin.syntax.Trees.Lambda => l }.flatMap { l =>
        TreeOps.nodes(l.param).collect { case v: hugin.syntax.Trees.VarRef => v.name }
      }.toSet
      val whereNames = TreeOps.nodes(source.where).collect { case v: hugin.syntax.Trees.VarRef => v.name }.toSet
      val name = if source.name.span.exists then source.name.span.text else f.name
      val texts = leaves.map { (p, lcl) =>
        val explicitBinds = lcl.binds.filter(!_._1.implicitBinder)
        val named = explicitBinds.collect { case (v, value, _) =>
          force(value) match
            case Val.Rigid(Head.Local(x), Nil) if p.isFree(x) => Some(x -> v.name)
            case _ => None
        }.flatten.toMap
        val refined = explicitBinds.filter((v, value, _) =>
          force(value) match
            case Val.Rigid(Head.Local(x), Nil) if p.isFree(x) => false
            case _ => true
        ).map((v, value, _) => v.name -> value).filter((n, _) => uses.exists(_.name == n))
        if refined.exists((n, _) => lambdaBound(n) || whereNames(n)) then None
        else
          val fresh = FreshNames(lcl.binds.map(_._1.name) ++ uses.map(_.name))
          val names = mutable.ArrayBuffer.tabulate(p.size)(l => named.getOrElse(l, "_"))
          val introduced = mutable.ListBuffer.empty[String]
          for (_, value) <- refined do
            val t = quote(p.size, value)
            for l <- (0 until p.size) if p.isFree(l) && names(l) == "_" && core.occurs(p.size - l - 1, t) do
              val base = p.names(l).filter(_.isLetter).capitalize
              names(l) = fresh(if base.isEmpty then "X" else base)
              introduced += names(l)
          val ns = names.toList.reverse
          val pats = f.explicit.drop(hidden).map(l => showArg(ns, explicitOnly(quote(p.size, p.values(l)))))
          val patTokens = pats.flatMap(_.split("[^A-Za-z0-9_']+")).toSet
          if !introduced.forall(patTokens) then None
          else
            val replacements = refined.toMap.view.mapValues { v =>
              val shown = showTm(ns, explicitOnly(quote(p.size, v)))
              if shown.contains(' ') then s"($shown)" else shown
            }.toMap
            val edits = uses.filter(u => replacements.contains(u.name)).sortBy(_.span.from)
            val rest = new StringBuilder
            var at = lhsEnd
            for u <- edits do
              rest ++= origin.content.substring(at, u.span.from)
              rest ++= replacements(u.name)
              at = u.span.until
            rest ++= origin.content.substring(at, source.span.until)
            Some((name :: pats).mkString(" ") + rest.toString)
      }
      if texts.contains(None) then None
      else Some(texts.flatten.mkString("\n" + " " * source.span.startCol))

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
