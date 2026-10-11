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
      /** The missing probes found so far (at most [[MaxMissing]]), and the cases of the tree they are below. */
      missingProbes: mutable.ListBuffer[SplitProblem] = mutable.ListBuffer.empty,
      missingNodes: mutable.ListBuffer[(SplitProblem, List[SplitProblem])] = mutable.ListBuffer.empty,
      /** The leaves found so far, per clause: its case and its state there. */
      leaves: mutable.HashMap[Int, mutable.ListBuffer[(SplitProblem, ClauseState)]] = mutable.HashMap.empty,
      /** Π: the positions at which some clause has a constructor, an atom or `()` (paths, last step first). */
      pi: mutable.Set[List[Int]] = mutable.Set.empty,
      /** The clause contexts, by clause. */
      contexts: mutable.ArrayBuffer[(SplitProblem, ClauseState)] = mutable.ArrayBuffer.empty,
      /** At the positions of Π with a numeral pattern: the literals and the offsets of the clauses there. */
      natPoints: mutable.HashMap[List[Int], (Set[BigInt], Set[BigInt])] = mutable.HashMap.empty
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
    for (p, _, cl) <- contexts do
      info.contexts += ((p, cl))
      inspected(info, p, cl)
    val checked = contexts.map { (p, t, cl) =>
      try checkClause(info, p, t, cl, speculative = false)
      catch case e: ElabError if !e.silent => throw withRefinementFix(e, info, problem, target, states, cl)
    }.toVector
    val tree =
      try buildTree(info, problem, target, states, leaf(info, checked))
      catch case _: ElabError if info.missingProbes.nonEmpty => notCovering(info, problem, target, clauses)
    if info.missingProbes.nonEmpty then notCovering(info, problem, target, clauses)
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
    reportInexact(info, checked)

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

  /** The outcome of splitting a problem by one clause alone ([[lhsSplit]]). */
  private enum Lhs:
    /** The clause context, its target type and the clause's state there. */
    case Context(p: SplitProblem, target: Val, cl: ClauseState)

    /** A pattern of the clause cannot occur: `pat` with the clause's state and the problem where it fails. */
    case Clash(p: SplitProblem, cl: ClauseState, pat: Pat, why: ClauseConflict)

    /** `()` where `found` (a constructor) is determined. */
    case NotEmpty(p: SplitProblem, cl: ClauseState, span: Span, found: Val)

    /** Every split of the clause is undecided: the first one's problem, constructor and equation. */
    case Undecided(p: SplitProblem, ctor: Int, a: Val, b: Val, span: Span)

  /** The problem split by `cl` alone, in the canonical order: the leftmost constructor position (by
   *  argument, then depth first) of the clause whose split is decided; a split whose index unification is
   *  stuck falls back to the next position (Agda's `altM1`). */
  @scala.annotation.tailrec
  private def lhsSplit(p: SplitProblem, target: Val, cl: ClauseState): Lhs =
    simplify(p, cl) match
      case Simplified.NoMatch(Pat.PAbsurd(span), term) => Lhs.NotEmpty(p, cl, span, term)
      case Simplified.NoMatch(pat, term) => Lhs.Clash(p, cl, pat, ClauseConflict.Argument(wild(p, term)))
      case Simplified.Ready(c) =>
        val candidates = c.eqns.filter(e => !isAbsurd(e.pat))
        if candidates.isEmpty then Lhs.Context(p, target, c)
        else
          // the first decided split, with the problem it gives
          var undecided: Option[Lhs.Undecided] = None
          var next: Option[Either[Lhs, (SplitProblem, Val)]] = None
          val it = candidates.iterator
          while next.isEmpty && it.hasNext do
            val e = it.next()
            val x = force(e.term) match
              case Val.Rigid(Head.Local(x), Nil) => x
              case _ => throw Impossible("split on a non-variable")
            e.pat match
              case Pat.PAtom(k, _) =>
                val p2 = p.solve(core, x, eval(Nil, k))
                next = Some(Right((p2, p2.norm(core, target))))
              case Pat.PLit(k, _) =>
                val p2 = p.solve(core, x, Val.Nat(natFamily(e.ty), k))
                next = Some(Right((p2, p2.norm(core, target))))
              case Pat.PSucc(_, j, _) =>
                val p1 = p.extend(p.names(x), p.types(x))
                val p2 = p1.solve(core, x, natSuccs(natType(e.ty).get._2, Val.local(p.size), j))
                next = Some(Right((p2, p2.norm(core, target))))
              case pat @ Pat.PCon(ctor, _, span) =>
                force(p.types(x)) match
                  case Val.Rigid(Head.Glob(fam), famSp) if isFamily(fam) =>
                    if !constructors(fam).contains(ctor) then
                      next = Some(Left(Lhs.Clash(p, c, pat, ClauseConflict.Family(wild(p, p.types(x))))))
                    else
                      val (p1, args, unified) = unifyConstructor(p, famSp, ctor)
                      unified match
                        case IndexUnification.Conflict(a, b) =>
                          next = Some(Left(Lhs.Clash(p, c, pat, ClauseConflict.Index(wild(p1, a), wild(p1, b)))))
                        case IndexUnification.Stuck(a, b) =>
                          if undecided.isEmpty then undecided = Some(Lhs.Undecided(p1, ctor, a, b, span))
                        case IndexUnification.Solved(p2) =>
                          val p3 = p2.solve(core, x, p2.norm(core, constructorApp(p2, ctor, args)))
                          next = Some(Right((p3, p3.norm(core, target))))
                  case other => fail(ClauseProblem.NotInductive(showVal(p.names.toList.reverse, other), span))
              case _ => throw Impossible("a stuck equation that is not a constructor pattern")
          next match
            case Some(Right((p2, t2))) => lhsSplit(p2, t2, c)
            case Some(Left(r)) => r
            case None => undecided.get

  /** The clause context of `cl`: the problem split by `cl` alone ([[lhsSplit]]), with `cl`'s state at its
   *  single leaf (its equations left are its absurd patterns, each against a variable of an empty type).
   *  E0915 if a constructor of the clause cannot occur (`only`: the clause is the function's only one), or
   *  if every split of the clause is undecided. */
  private def clauseContext(p: SplitProblem, target: Val, cl: ClauseState, only: Boolean): (SplitProblem, Val, ClauseState) =
    lhsSplit(p, target, cl) match
      case Lhs.Context(p1, t1, c) =>
        c.eqns.foreach(checkAbsurd(p1, _))
        (p1, t1, c)
      case Lhs.NotEmpty(p1, c, span, term) =>
        fail(ClauseProblem.AbsurdNotEmpty(wild(p1, p1.norm(core, typeAt(p1, c, span))), List(headName(term)), span))
      case Lhs.Clash(p1, c, pat, why) => fail(impossible(p1, c, pat, why, only))
      case Lhs.Undecided(p1, ctor, a, b, span) => fail(undecidable(p1, ctor, a, b, span))

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
      // in the file's text: an item may be a slice of it, which ends at the item
      val file = span.source
      val text = file.content
      var from = span.start
      while from > 0 && (text(from - 1) == ' ' || text(from - 1) == '\t') do from -= 1
      var until = span.end
      while until < text.length && (text(until) == ' ' || text(until) == '\t') do until += 1
      val startsLine = from == 0 || text(from - 1) == '\n'
      val endsLine = until >= text.length || text(until) == '\n'
      if startsLine && endsLine then Span(file, from, (until + 1).min(text.length)) else span

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
        case pat @ (_: Pat.PLit | _: Pat.PSucc | _: Pat.PCon) if natType(e.ty).exists((z, s) =>
              pat match
                case Pat.PCon(c, _, _) => c == z || c == s
                case _ => true
            ) =>
          // against a nat-like family: as a numeral, matched by value (reference: meta/clauses)
          val (z, s) = natType(e.ty).get
          natForm(pat, z, s) match
            case NatPattern.Offset(q, j) if j == 0 => pending = e.copy(pat = q) :: pending
            case np =>
              natMatch(p, e, np, s) match
                case NatMatch.Clash(term) => clash = Simplified.NoMatch(e.pat, term)
                case NatMatch.Stuck(eqn) => stuck += eqn
                case NatMatch.Next(eqn) => pending = eqn :: pending
                case NatMatch.Done =>
        case Pat.PAtom(key, span) =>
          force(e.term) match
            case Val.Rigid(Head.Local(x), Nil) if p.isFree(x) => stuck += e
            case other =>
              atomKey(other) match
                case Some(k) => if k != key then clash = Simplified.NoMatch(e.pat, other)
                case None => fail(ClauseProblem.CannotMatchArgument(showVal(p.names.toList.reverse, other), span))
        case Pat.PLit(_, span) => fail(ClauseProblem.LiteralPattern(showVal(p.names.toList.reverse, e.ty), span))
        case Pat.PSucc(_, _, span) => fail(ClauseProblem.LiteralPattern(showVal(p.names.toList.reverse, e.ty), span))
        case Pat.PCon(c, args, span) =>
          forceView(e.term) match
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

  /** The outcome of matching a numeral pattern ([[natMatch]]). */
  private enum NatMatch:
    case Clash(term: Val)

    /** The pattern, the rest of it, against a free variable. */
    case Stuck(eqn: Eqn)

    /** The pattern under the offset against the value under it. */
    case Next(eqn: Eqn)
    case Done

  /** A numeral pattern against the term of `e` (of the nat-like family with the successor `s`), by value: a
   *  literal against a numeral compares them, an offset `p + j` subtracts; successors applied to a free
   *  variable are taken off first. A literal the variable's range excludes, or an offset at least its
   *  bound, clashes. */
  private def natMatch(p: SplitProblem, e: Eqn, np: NatPattern, s: Int): NatMatch =
    val term = force(e.term)
    natChain(term) match
      case Left(m) =>
        np match
          case NatPattern.Literal(k, _) => if k == m then NatMatch.Done else NatMatch.Clash(term)
          case NatPattern.Offset(q, j) =>
            if m >= j then NatMatch.Next(Eqn(Val.Nat(natFamily(e.ty), m - j), q, e.ty)) else NatMatch.Clash(term)
      case Right((i, base)) =>
        val freeVar = base match
          case Val.Rigid(Head.Local(x), Nil) if p.isFree(x) => Some(x)
          case _ => None
        np match
          case NatPattern.Literal(k, span) =>
            if k < i then NatMatch.Clash(term)
            else
              freeVar match
                case Some(x) =>
                  if p.range(x).allows(k - i) then NatMatch.Stuck(Eqn(base, Pat.PLit(k - i, span), e.ty)) else NatMatch.Clash(term)
                case None => fail(ClauseProblem.CannotMatchArgument(showVal(p.names.toList.reverse, term), span))
          case NatPattern.Offset(q, j) =>
            if j <= i then NatMatch.Next(Eqn(natSuccs(s, base, i - j), q, e.ty))
            else
              freeVar match
                case Some(x) =>
                  if p.range(x).below.exists(_ <= j - i) then NatMatch.Clash(term)
                  else NatMatch.Stuck(Eqn(base, Pat.PSucc(q, j - i, Span.NoSpan), e.ty))
                case None => fail(ClauseProblem.CannotMatchArgument(showVal(p.names.toList.reverse, term), Span.NoSpan))

  /** The nat-like family a type is. */
  private def natFamily(ty: Val): Int = force(ty) match
    case Val.Rigid(Head.Glob(f), _) => f
    case _ => throw Impossible("not a nat-like type")

  /** A stuck numeral pattern (a literal or an offset of at least 1) against a free variable. */
  private def isNatEqn(e: Eqn): Boolean = e.pat match
    case _: Pat.PLit | _: Pat.PSucc => true
    case _ => false

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

  /** The tree of the cases below `p` for the clauses that may still apply. Below a variable none of whose
   *  constructors can occur (`refuted`), the analysis goes on with the clauses that have no constructor
   *  there, for W0006 (a clause matching only refuted probes is reachable), and emits nothing. */
  private def buildTree(
      f: FunctionInfo,
      p: SplitProblem,
      target: Val,
      clauses: List[ClauseState],
      leaf: LeafBuilder,
      refuted: Boolean = false
  ): CaseTree =
    if p.dead then Discarded
    else clauses.iterator.map(simplify(p, _)).collect { case Simplified.Ready(cl) => cl }.toList match
      case Nil => if refuted then Discarded else absurdSplit(p).getOrElse(missingNode(f, p))
      case first :: _ if first.eqns.isEmpty =>
        f.used += first.index
        if refuted then Discarded
        else
          f.leaves.getOrElseUpdate(first.index, mutable.ListBuffer.empty) += ((p, first))
          leaf(p, first)
      case all @ (first :: _) =>
        // the canonical order: the leftmost position of the first clause whose split is decided; an
        // absurd pattern splits only when the clause has no other constructor pattern left
        val nonAbsurd = first.eqns.filter(e => !isAbsurd(e.pat))
        val candidates = if nonAbsurd.isEmpty then List(first.eqns.head) else nonAbsurd
        var undecided: Option[ClauseProblem] = None
        var result: Option[CaseTree] = None
        val it = candidates.iterator
        while result.isEmpty && it.hasNext do
          val e = it.next()
          val x = force(e.term) match
            case Val.Rigid(Head.Local(x), Nil) => x
            case _ => throw Impossible("split on a non-variable")
          e.pat match
            case _: Pat.PAtom => result = Some(splitAtom(f, p, x, target, all, leaf, refuted))
            case _: Pat.PLit | _: Pat.PSucc => result = Some(splitNat(f, p, x, e.ty, target, all, leaf, refuted))
            case pat =>
              val span = pat match
                case Pat.PCon(_, _, s) => s
                case Pat.PAbsurd(s) => s
                case _ => first.source.span
              force(p.types(x)) match
                case Val.Rigid(Head.Glob(fam), famSp) if isFamily(fam) =>
                  val unified = constructors(fam).map(c => (c, unifyConstructor(p, famSp, c)))
                  unified.collectFirst { case (c, (p1, _, IndexUnification.Stuck(a, b))) => undecidable(p1, c, a, b, span) } match
                    case Some(problem) => if undecided.isEmpty then undecided = Some(problem)
                    case None => result = Some(split(f, p, x, target, all, unified, leaf, refuted))
                case other =>
                  if refuted then result = Some(Discarded)
                  else fail(ClauseProblem.NotInductive(showVal(p.names.toList.reverse, other), span))
        result.getOrElse(if refuted then Discarded else fail(undecided.get))

  /** The tree of a case that no evaluation reaches (the analysis below an empty variable). */
  private val Discarded: CaseTree = CaseTree.Split(-1, Nil)

  /** Splits on variable `x`: a branch per constructor whose indices unify (`unified`: each constructor of
   *  its type with its index unification, none stuck). If none can occur, the analysis goes on below the
   *  empty variable with the clauses that have no constructor at it. */
  private def split(
      f: FunctionInfo,
      p: SplitProblem,
      x: Int,
      target: Val,
      clauses: List[ClauseState],
      unified: List[(Int, (SplitProblem, List[(Val, Icit)], IndexUnification))],
      leaf: LeafBuilder,
      refuted: Boolean
  ): CaseTree =
    val branches = unified.collect { case (c, (_, args, IndexUnification.Solved(p2))) =>
      val p3 = p2.solve(core, x, p2.norm(core, constructorApp(p2, c, args)))
      CaseBranch(c, args.length, buildTree(f, p3, p3.norm(core, target), clauses, leaf, refuted))
    }
    if branches.isEmpty then
      val rest = clauses.filterNot(_.eqns.exists(e => force(e.term) == Val.local(x)))
      buildTree(f, p, target, rest, leaf, refuted = true)
    CaseTree.Split(x, branches)

  /** Splits on variable `x` of a nat-like type by value (reference: meta/clauses, "Evaluation"; Agda's
   *  literal branches, Lean's `caseValues`): a branch per literal that a remaining clause has against `x`;
   *  then, if some clause has an offset `p + j` against `x`, a branch for the values of at least the least
   *  offset `j`, with `x := y + j` for a new variable `y`, and a branch for the other values below `j`;
   *  otherwise a branch for every other value. The clauses with literals do not apply in the branches
   *  that are not their values', nor the clauses with offsets in the branch below. */
  private def splitNat(
      f: FunctionInfo,
      p: SplitProblem,
      x: Int,
      ty: Val,
      target: Val,
      clauses: List[ClauseState],
      leaf: LeafBuilder,
      refuted: Boolean
  ): CaseTree =
    val fam = natFamily(ty)
    val s = natLike(fam).get._2
    def on(cl: ClauseState) = cl.eqns.find(e => isNatEqn(e) && force(e.term) == Val.local(x)).map(_.pat)
    val literals = clauses.flatMap(on).collect { case Pat.PLit(k, _) => k }.distinct.sorted
    val offset = clauses.flatMap(on).collect { case Pat.PSucc(_, j, _) => j }.minOption.getOrElse(BigInt(0))
    val values = literals.filter(p.range(x).allows).map { k =>
      val p2 = p.solve(core, x, Val.Nat(fam, k))
      (k, buildTree(f, p2, p2.norm(core, target), clauses, leaf, refuted))
    }
    val rest = clauses.filterNot(cl => on(cl).exists(_.isInstanceOf[Pat.PLit]))
    val others = NatRange(literals.toSet, None)
    if offset > 0 then
      val p1 = p.extend(p.names(x), p.types(x))
      val p2 = p1.solve(core, x, natSuccs(s, Val.local(p.size), offset))
      val above = buildTree(f, p2, p2.norm(core, target), rest, leaf, refuted)
      val p3 = p.restrict(x, others.meet(NatRange(Set.empty, Some(offset))))
      val below = buildTree(f, p3, target, rest.filterNot(cl => on(cl).exists(_.isInstanceOf[Pat.PSucc])), leaf, refuted)
      CaseTree.SplitNat(x, fam, values, offset, above, below)
    else
      val p3 = p.restrict(x, others)
      CaseTree.SplitNat(x, fam, values, BigInt(0), Discarded, buildTree(f, p3, target, rest, leaf, refuted))

  /** Splits on variable `x` of a type without constructors but with decidable equality: a branch per value
   *  that a clause matches it against, and a default branch for the clauses that do not. */
  private def splitAtom(
      f: FunctionInfo,
      p: SplitProblem,
      x: Int,
      target: Val,
      clauses: List[ClauseState],
      leaf: LeafBuilder,
      refuted: Boolean
  ): CaseTree =
    def atomOn(e: Eqn) = e.pat.isInstanceOf[Pat.PAtom] && force(e.term) == Val.local(x)
    val keys = clauses.flatMap(_.eqns.filter(atomOn)).collect { case Eqn(_, Pat.PAtom(k, _), _) => k }.distinct
    val branches = keys.map { k =>
      val p2 = p.solve(core, x, eval(Nil, k))
      (k, buildTree(f, p2, p2.norm(core, target), clauses, leaf, refuted))
    }
    CaseTree.SplitAtom(x, branches, buildTree(f, p, target, clauses.filterNot(_.eqns.exists(atomOn)), leaf, refuted))

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
      // a numeral is closed: no variable of the clause in it
      case Val.Nat(_, _) =>
      // successors over a variable of the clause: the leaf's value with as many successors taken off
      case n @ Val.NatAdd(fam, _, _) =>
        natChain(n) match
          case Right((i, base)) =>
            natChain(b) match
              case Left(m) => if m >= i then go(base, Val.Nat(fam, m - i))
              case Right((j, bb)) => if j >= i then go(base, natAdd(fam, bb, j - i))
          case Left(_) =>
      case Val.Rigid(Head.Glob(c), sp) if isConstructor(c) =>
        forceView(b) match
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
    val targets = order.map(l =>
      force(sub(l)) match
        case Val.Rigid(Head.Local(y), Nil) if p.isFree(y) => y
        case _ => -1
    )
    !targets.contains(-1) && targets.distinct.length == targets.length && targets.length == (0 until p.size).count(p.isFree)

  /** For a clause with calls whose leaves refine its clause context: its calls at its leaves, which the
   *  termination check uses for a fix that writes out the clause's cases ([[SizeChange]]). */
  private def alternativeCalls(f: FunctionInfo, ch: Checked): Unit = ch.rhs match
    case Some(rhs) if rhs.calls =>
      val leaves = expandedLeaves(f.leaves.get(ch.state.index).map(_.toList).getOrElse(Nil)).getOrElse(Nil)
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
  private def withRefinementFix(
      e: ElabError,
      f: FunctionInfo,
      problem: SplitProblem,
      target: Val,
      states: List[ClauseState],
      cl: ClauseState
  ): ElabError =
    if cl.source.where.nonEmpty || cl.absurd then e
    else
      val probe = f.copy(
        used = mutable.Set.empty,
        missingProbes = mutable.ListBuffer.empty,
        missingNodes = mutable.ListBuffer.empty,
        leaves = mutable.HashMap.empty
      )
      val built =
        try
          buildTree(probe, problem, target, states, (_, _) => CaseTree.Split(-1, Nil))
          true
        catch case _: ElabError => false
      val leaves = expandedLeaves(probe.leaves.get(cl.index).map(_.toList).getOrElse(Nil)).getOrElse(Nil)
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
            val help = "the clause is checked in its own context, without the refinement made by the clauses before it"
            ElabError(
              e.diag.copy(helps = e.diag.helps :+ fix.message, notes = e.diag.notes :+ help, suggestions = e.diag.suggestions :+ fix),
              e.unresolved,
              e.silent
            )
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
    if !source.span.exists || written.exists(t => !t.span.exists || TreeOps.nodes(t).exists(_.isInstanceOf[hugin.syntax.Trees.Quote])) then
      None
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
          for (v, value) <- refined do
            val t = quote(p.size, value)
            for l <- (0 until p.size) if p.isFree(l) && names(l) == "_" && core.occurs(p.size - l - 1, t) do
              names(l) = fresh(v)
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

  // ---------------------------------------------------------------- probes and missing cases

  /** The positions of `v` (an argument's value, at `path`), each with the value there: a constructor
   *  application's explicit arguments are its children (paths are lists, the last step first). A value of
   *  a nat-like family (a numeral, or successors applied to a value) is one position: its patterns are
   *  numerals ([[Patterns.natForm]]). */
  private def walk(v: Val, path: List[Int], visit: (List[Int], Val) => Unit): Unit =
    val f = force(v)
    visit(path, f)
    f match
      case Val.Nat(_, _) | Val.NatAdd(_, _, _) =>
      case Val.Rigid(Head.Glob(c), _) if isSuccessor(c) || constantOf(c) =>
      case Val.Rigid(Head.Glob(c), sp) if isConstructor(c) =>
        sp.reverse.collect { case Elim.EApp(a, Icit.Expl) => a }.zipWithIndex.foreach((a, k) => walk(a, k :: path, visit))
      case _ =>

  /** Whether `v` (forced) is a numeral or a successor application. */
  private def natValue(v: Val): Boolean = v match
    case Val.Nat(_, _) | Val.NatAdd(_, _, _) => true
    case Val.Rigid(Head.Glob(c), _) => isSuccessor(c) || constantOf(c)
    case _ => false

  /** Adds the positions that clause `cl` inspects in its context `p` to Π: its constructors, numerals and
   *  atoms, and its absurd patterns; at a numeral position, its literal or offset. */
  private def inspected(f: FunctionInfo, p: SplitProblem, cl: ClauseState): Unit =
    val absurdVars =
      cl.eqns.collect { case Eqn(t, Pat.PAbsurd(_), _) => force(t) }.collect { case Val.Rigid(Head.Local(x), Nil) => x }.toSet
    def point(path: List[Int], literal: Option[BigInt], offset: Option[BigInt]): Unit =
      val (ls, os) = f.natPoints.getOrElse(path, (Set.empty[BigInt], Set.empty[BigInt]))
      f.natPoints(path) = (ls ++ literal, os ++ offset)
      f.pi += path
    for l <- 0 until f.arity do
      walk(
        p.values(l),
        List(l),
        (path, v) =>
          v match
            case n if natValue(n) =>
              natChain(n) match
                case Left(m) => point(path, Some(m), None)
                case Right((i, _)) => if i > 0 then point(path, None, Some(i))
            case Val.Rigid(Head.Glob(c), _) if isConstructor(c) => f.pi += path
            case Val.Rigid(Head.Local(x), Nil) if absurdVars(x) => f.pi += path
            case other => if atomKey(other).isDefined then f.pi += path
      )

  /** A variable to split for the probes: of an inductive family by its constructors, or of a nat-like
   *  family by value classes, `shift` successors below a position of Π. */
  private enum ToSplit:
    case Constructors(x: Int)
    case Values(x: Int, path: List[Int], shift: BigInt)

  /** The leftmost free variable of `p` at a position of Π whose type is an inductive family (by argument,
   *  then depth first), other than those in `skip`. */
  private def splittable(f: FunctionInfo, p: SplitProblem, skip: Set[Int]): Option[ToSplit] =
    var found: Option[ToSplit] = None
    def free(v: Val) = v match
      case Val.Rigid(Head.Local(x), Nil) if p.isFree(x) && !skip(x) => Some(x)
      case _ => None
    for l <- 0 until f.arity do
      walk(
        p.values(l),
        List(l),
        (path, v) =>
          if found.isEmpty && f.pi(path) then
            v match
              case n if natValue(n) =>
                natChain(n) match
                  case Right((i, base)) => free(base).foreach(x => found = Some(ToSplit.Values(x, path, i)))
                  case Left(_) =>
              case other =>
                free(other).foreach { x =>
                  force(p.types(x)) match
                    case Val.Rigid(Head.Glob(fam), _) if natLike(fam).isDefined => found = Some(ToSplit.Values(x, path, BigInt(0)))
                    case Val.Rigid(Head.Glob(fam), _) if isFamily(fam) => found = Some(ToSplit.Constructors(x))
                    case _ =>
                }
      )
    found

  /** The value classes of the variable `x` of a nat-like family, `shift` successors below the position
   *  `path`, in the case `q` (reference: meta/coverage, "Cases and probes"): at the clauses' literals `l`
   *  and offsets `j` there, the numerals are cut into the singletons and intervals that no clause tells
   *  apart. A singleton or a bounded interval gives its numerals (which the range of `x` allows); the
   *  unbounded interval from `a` gives `x := z + a` for a new variable `z`, or, from 0, leaves `x`. */
  private def valueClasses(f: FunctionInfo, q: SplitProblem, x: Int, path: List[Int], shift: BigInt): Iterator[Either[SplitProblem, Unit]] =
    val (ls, os) = f.natPoints.getOrElse(path, (Set.empty[BigInt], Set.empty[BigInt]))
    val lits = ls.collect { case l if l >= shift => l - shift }
    val offs = os.collect { case j if j > shift => j - shift }
    val cuts = (Set(BigInt(0)) ++ lits ++ lits.map(_ + 1) ++ offs).toList.sorted
    val r = q.range(x)
    val fam = natFamily(q.types(x))
    val s = natLike(fam).get._2
    def value(v: BigInt): Iterator[Either[SplitProblem, Unit]] =
      if r.allows(v) then Iterator(Left(q.solve(core, x, Val.Nat(fam, v)))) else Iterator.empty
    def interval(a: BigInt, b: BigInt): Iterator[Either[SplitProblem, Unit]] =
      Iterator.iterate(a)(_ + 1).takeWhile(_ < b).flatMap(value)
    val bounded = cuts.zip(cuts.tail).iterator.flatMap((a, b) => interval(a, b))
    val last = cuts.last
    val unbounded: Iterator[Either[SplitProblem, Unit]] = r.below match
      case Some(b) => interval(last, b)
      case None =>
        if last == 0 then Iterator(Right(()))
        else
          Iterator.single(()).map { _ =>
            val q1 = q.extend(q.names(x), q.types(x))
            Left(q1.solve(core, x, natSuccs(s, Val.local(q.size), last)))
          }
    bounded ++ unbounded

  /** The probes below the case `p` (reference: meta/coverage, "Cases and probes"), in the canonical order:
   *  `p` split at its variables at positions of Π until none can be split. A variable none of whose
   *  constructors can occur is *empty*, and its probes are *refuted*; an undecided split is skipped (its
   *  case is not refuted). A variable of a nat-like family splits into its value classes. `visit` gets
   *  each probe and whether it is refuted, and returns whether to go on; the enumeration stops after
   *  [[MaxProbeSteps]] splits (`false`). */
  private def probes(f: FunctionInfo, p: SplitProblem)(visit: (SplitProblem, Boolean) => Boolean): Boolean =
    var stack: List[Iterator[(SplitProblem, Set[Int], Boolean)]] = List(Iterator((p, Set.empty[Int], false)))
    var steps = 0
    var go = true
    while go && stack.nonEmpty do
      if !stack.head.hasNext then stack = stack.tail
      else
        val (q, skip, refuted) = stack.head.next()
        if q.dead then ()
        else
          splittable(f, q, skip) match
            case None => go = visit(q, refuted)
            case Some(target) =>
              steps += 1
              if steps > MaxProbeSteps then go = false
              else
                target match
                  case ToSplit.Values(x, path, shift) =>
                    stack = valueClasses(f, q, x, path, shift).map {
                      case Left(q2) => (q2, skip, refuted)
                      case Right(()) => (q, skip + x, refuted)
                    } :: stack
                  case ToSplit.Constructors(x) =>
                    force(q.types(x)) match
                      case Val.Rigid(Head.Glob(fam), famSp) =>
                        val unified = constructors(fam).map(c => (c, unifyConstructor(q, famSp, c)))
                        if unified.exists(_._2._3.isInstanceOf[IndexUnification.Stuck]) then
                          stack = Iterator((q, skip + x, refuted)) :: stack
                        else
                          val cases = unified.collect { case (c, (_, args, IndexUnification.Solved(q2))) =>
                            q2.solve(core, x, q2.norm(core, constructorApp(q2, c, args)))
                          }
                          if cases.isEmpty then stack = Iterator((q, skip + x, true)) :: stack
                          else stack = cases.iterator.map(c => (c, skip, refuted)) :: stack
                      case _ => stack = Iterator((q, skip + x, refuted)) :: stack
    go && steps <= MaxProbeSteps

  /** A case of the tree that no clause applies to: its probes that are not refuted are missing (at most
   *  [[MaxMissing]] in all). If every probe is refuted, the case needs no clause, and the tree has an
   *  empty split there. */
  private def missingNode(f: FunctionInfo, p: SplitProblem): CaseTree =
    var missing = false
    var emptyVar: Option[Int] = None
    val mine = mutable.ListBuffer.empty[SplitProblem]
    val complete = probes(f, p) { (q, refuted) =>
      if refuted then
        if emptyVar.isEmpty then emptyVar = (0 until p.size).find(p.isFree)
      else
        missing = true
        f.missingProbes += q
        mine += q
      f.missingProbes.length < MaxMissing
    }
    // too many splits: the case itself counts as missing
    if !complete && !missing then
      missing = true
      f.missingProbes += p
      mine += p
    if missing then
      f.missingNodes += ((p, mine.toList))
      if f.missingProbes.length >= MaxMissing then fail(ClauseProblem.NotCovering(f.name, "", globals(f.id).span, 0))
      Discarded
    else CaseTree.Split(emptyVar.getOrElse(0), Nil)

  private val MaxMissing = 20
  private val MaxProbeSteps = 2000

  /** A pattern of a missing case, over the explicit arguments: a wildcard, a constructor applied to the
   *  patterns of its explicit arguments, or an atom (its key). */
  private enum MPat:
    case Wild
    case Con(c: Int, args: List[MPat])
    case Atom(key: Tm)

    /** The numeral `k` of the nat-like family `fam`. */
    case Lit(fam: Int, k: BigInt)

    /** `_ + j` (`j ≥ 1`) of the nat-like family with the successor `suc`. */
    case Succ(suc: Int, j: BigInt)

  private def toMPat(v: Val): MPat =
    val f = force(v)
    if natValue(f) then
      val fam = f match
        case Val.Nat(fam, _) => fam
        case Val.NatAdd(fam, _, _) => fam
        case Val.Rigid(Head.Glob(c), _) =>
          globals(c).kind match
            case GlobalKind.Constructor(fam) => fam
            case _ => -1
        case _ => -1
      natChain(f) match
        case Left(m) => MPat.Lit(fam, m)
        case Right((i, _)) => if i > 0 then MPat.Succ(natLike(fam).get._2, i) else MPat.Wild
    else
      f match
        case Val.Rigid(Head.Glob(c), sp) if isConstructor(c) => MPat.Con(c, sp.reverse.collect { case Elim.EApp(a, Icit.Expl) => toMPat(a) })
        case other => atomKey(other).fold(MPat.Wild)(MPat.Atom(_))

  /** The explicit arguments of a case as patterns. */
  private def patternsOf(f: FunctionInfo, p: SplitProblem): List[MPat] = f.explicit.map(l => toMPat(p.values(l)))

  private def toPat(m: MPat): Pat = m match
    case MPat.Wild => Pat.PWild(Span.NoSpan)
    case MPat.Con(c, as) => Pat.PCon(c, as.map(toPat), Span.NoSpan)
    case MPat.Atom(k) => Pat.PAtom(k, Span.NoSpan)
    case MPat.Lit(_, k) => Pat.PLit(k, Span.NoSpan)
    case MPat.Succ(_, j) => Pat.PSucc(Pat.PWild(Span.NoSpan), j, Span.NoSpan)

  /** The common instance of two patterns, if they do not clash. */
  private def merge(a: MPat, b: MPat): Option[MPat] = (a, b) match
    case (MPat.Wild, _) => Some(b)
    case (_, MPat.Wild) => Some(a)
    case (MPat.Con(c, as), MPat.Con(d, bs)) if c == d && as.length == bs.length =>
      val ms = as.zip(bs).map(merge)
      Option.when(ms.forall(_.isDefined))(MPat.Con(c, ms.flatten))
    case (MPat.Atom(k), MPat.Atom(j)) if k == j => Some(a)
    case (MPat.Lit(_, k), MPat.Lit(_, j)) if k == j => Some(a)
    case (MPat.Lit(_, k), MPat.Succ(_, j)) => Option.when(k >= j)(a)
    case (MPat.Succ(_, j), MPat.Lit(_, k)) => Option.when(k >= j)(b)
    case (MPat.Succ(_, i), MPat.Succ(_, j)) => Some(if i >= j then a else b)
    case _ => None

  /** `a` is an instance of `b`. */
  private def instanceOf(a: MPat, b: MPat): Boolean = (a, b) match
    case (_, MPat.Wild) => true
    case (MPat.Con(c, as), MPat.Con(d, bs)) => c == d && as.length == bs.length && as.zip(bs).forall(instanceOf)
    case (MPat.Atom(k), MPat.Atom(j)) => k == j
    case (MPat.Lit(_, k), MPat.Lit(_, j)) => k == j
    case (MPat.Lit(_, k), MPat.Succ(_, j)) => k >= j
    case (MPat.Succ(_, i), MPat.Succ(_, j)) => i >= j
    case _ => false

  /** The ordering of missing patterns: argument by argument, `_` first, constructors in declaration order. */
  private def compareM(a: MPat, b: MPat): Int = (a, b) match
    case (MPat.Wild, MPat.Wild) => 0
    case (MPat.Wild, _) => -1
    case (_, MPat.Wild) => 1
    case (MPat.Con(c, as), MPat.Con(d, bs)) =>
      if c != d then c.compare(d) else compareAll(as, bs)
    // numerals as their unary terms: `0` (the constant) before the successor, `_` before a constructor
    case (MPat.Lit(_, k), MPat.Lit(_, j)) => k.compare(j)
    case (MPat.Succ(_, i), MPat.Succ(_, j)) => i.compare(j)
    case (MPat.Lit(_, k), MPat.Succ(_, j)) => if k < j then -1 else 1
    case (MPat.Succ(_, j), MPat.Lit(_, k)) => if k < j then 1 else -1
    case (MPat.Con(_, _), _) => -1
    case (_, MPat.Con(_, _)) => 1
    case (MPat.Atom(k), MPat.Atom(j)) => showTm(Nil, k).compare(showTm(Nil, j))
    case (MPat.Atom(_), _) => -1
    case (_, MPat.Atom(_)) => 1

  private def compareAll(as: List[MPat], bs: List[MPat]): Int =
    as.zip(bs).iterator.map(compareM).find(_ != 0).getOrElse(as.length.compare(bs.length))

  /** The most general missing patterns `M` (reference: meta/coverage, "Missing cases"): the
   *  generalizations of the missing cases of the tree (a subpattern replaced by `_`, as long as no clause
   *  matches a probe below), maximal, in the order of [[compareM]]. Whether a clause matches a probe below a
   *  pattern is decided pairwise: their common instance, if they do not clash, is split by index
   *  unification ([[lhsSplit]]); a common instance whose splits are undecided counts as matched. */
  private def mostGeneralMissing(f: FunctionInfo, problem: SplitProblem, target: Val): List[List[MPat]] =
    val clausePatterns = f.contexts.toList.collect { case (p, cl) if !cl.absurd => patternsOf(f, p) }
    val feasible = mutable.HashMap.empty[List[MPat], Boolean]
    def possible(m: List[MPat]): Boolean = feasible.getOrElseUpdate(
      m, {
        val pats = m.iterator
        val eqns = (0 until f.arity).toList.map { l =>
          val pat = if f.explicit.contains(l) then toPat(pats.next()) else Pat.PWild(Span.NoSpan)
          Eqn(Val.local(l), pat, problem.types(l))
        }
        val st = ClauseState(-1, eqns, Nil, f.contexts.head._2.source)
        try
          lhsSplit(problem, target, st) match
            case _: Lhs.Clash => false
            case _ => true
        catch case _: ElabError => true
      }
    )
    def uncovered(q: List[MPat]): Boolean = clausePatterns.forall { cp =>
      val ms = q.zip(cp).map(merge)
      !ms.forall(_.isDefined) || !possible(ms.flatten)
    }

    /** The patterns with one constructor or atom replaced by `_`, in preorder. */
    // the numerals at which a generalization of a numeral can change whether a clause matches below it
    val cuts = (clausePatterns.flatten.flatMap(numbers) ++ List(BigInt(0))).distinct.sorted
    def offsets(s: Int, below: BigInt): List[MPat] =
      cuts.filter(_ < below).map(d => if d == 0 then MPat.Wild else MPat.Succ(s, d))
    def steps(q: List[MPat]): List[List[MPat]] =
      def one(m: MPat): List[MPat] = m match
        case MPat.Wild => Nil
        case MPat.Atom(_) => List(MPat.Wild)
        // `k` is `suc^k zero`, `_ + j` is `suc^j _`: a subterm replaced by `_` is `_ + d` for a smaller `d`
        case MPat.Lit(fam, k) => offsets(natLike(fam).get._2, k + 1)
        case MPat.Succ(s, j) => offsets(s, j)
        case MPat.Con(c, as) => MPat.Wild :: as.indices.toList.flatMap(i => one(as(i)).map(a => MPat.Con(c, as.updated(i, a))))
      q.indices.toList.flatMap(i => one(q(i)).map(a => q.updated(i, a)))
    var budget = 5000
    val maximal = mutable.LinkedHashSet.empty[List[MPat]]
    val visited = mutable.HashSet.empty[List[MPat]]
    def generalize(q: List[MPat]): Unit =
      val next = if budget <= 0 then Nil
      else
        steps(q).filter { n =>
          budget -= 1; uncovered(n)
        }
      if next.isEmpty then maximal += q
      else for n <- next if visited.add(n) do generalize(n)
    // from a missing case of the tree, or from its probes if it has a variable with a range (the case is
    // not a pattern then)
    for (node, below) <- f.missingNodes do
      val starts = if (0 until node.size).exists(x => node.isFree(x) && node.ranges.contains(x)) then below else List(node)
      for start <- starts do
        val q = patternsOf(f, start)
        if visited.add(q) then generalize(q)
    val all = maximal.toList
    all.filterNot(q => all.exists(r => r != q && q.zip(r).forall(instanceOf))).sortWith(compareAll(_, _) < 0)

  /** The numerals in a pattern, and one more than each (where an interval of numerals starts). */
  private def numbers(m: MPat): List[BigInt] = m match
    case MPat.Lit(_, k) => List(k, k + 1)
    case MPat.Succ(_, j) => List(j)
    case MPat.Con(_, as) => as.flatMap(numbers)
    case _ => Nil

  /** A missing pattern as the left-hand side of a clause: the hidden arguments of a lifted function are
   *  not written by users ([[Lifting]]). */
  private def showMissing(f: FunctionInfo, q: List[MPat]): String =
    def term(m: MPat): Tm = m match
      case MPat.Wild => Tm.Var(0)
      case MPat.Con(c, as) => as.foldLeft(Tm.Global(c): Tm)((acc, a) => Tm.App(acc, term(a), Icit.Expl))
      case MPat.Atom(k) => k
      case MPat.Lit(fam, k) => Tm.Nat(fam, k)
      // `_ + j` printed as the sum it is
      case MPat.Succ(_, j) => Tm.Arith(hugin.obj.ArithOp.Add, Tm.Var(0), Tm.Nat(-1, j), Stage.S1)
    val args = q.drop(globals(f.id).hidden).map { m =>
      val s = showTm(List("_"), term(m))
      if s.contains(' ') then s"($s)" else s
    }
    (f.name :: args).mkString(" ")

  /** E0911 with the first of the most general missing patterns and their number; tooling gets a cover of
   *  the missing probes by them, without redundant patterns, in their order (at most [[MaxMissing]]). */
  private def notCovering(f: FunctionInfo, problem: SplitProblem, target: Val, clauses: List[SurfaceClause]): Nothing =
    val declared = globals(f.id).span
    val general = mostGeneralMissing(f, problem, target)
    val probes = f.missingProbes.toList.map(patternsOf(f, _))
    val cover = mutable.ListBuffer.empty[List[MPat]]
    for q <- general if cover.length < MaxMissing do
      def below(r: List[MPat])(pr: List[MPat]) = pr.zip(r).forall(instanceOf)
      if probes.exists(pr => below(q)(pr) && !cover.exists(c => below(c)(pr))) then cover += q
    val shown = general.map(showMissing(f, _))
    if f.name.forall(ch => ch.isLetterOrDigit || ch == '_' || ch == '\'') && clauses.nonEmpty && !index.muted then
      index.meta.missing(
        MetaIndex.MissingClauses(declared, f.name, cover.toList.map(showMissing(f, _) + " = ?."), clauses.map(_.span).maxBy(_.end))
      )
    fail(ClauseProblem.NotCovering(f.name, shown.headOption.getOrElse(f.name), declared, (shown.length - 1).max(0)))

  // ---------------------------------------------------------------- inexact clauses (#67 batch 3)

  /** The opt-in lint `inexact_clauses` (W0009), Agda's `--exact-split`: a clause *holds definitionally*
   *  iff it is the leaf of exactly one case of the tree and that case is its clause context (the matching
   *  substitution renames). Otherwise an application that matches the clause's patterns may not evaluate
   *  by it (reference: meta/clauses, "Evaluation"). The diagnostic is always computed, as every lint; its
   *  level, off by default, applies when it is shown. Absurd and unreachable clauses have no leaf; clauses
   *  without a position (generated ones) and those of the bundled library (whose catch-all clauses are
   *  deliberate, and which users cannot change) are not reported. */
  private def reportInexact(f: FunctionInfo, checked: Vector[Checked]): Unit =
    def linted(sp: Span) = sp.exists && !hugin.compiler.StdlibCache.isStdlib(sp.source.path)
    for ch <- checked if !ch.state.absurd && linted(ch.state.source.span) do
      f.leaves.get(ch.state.index).map(_.toList).getOrElse(Nil) match
        case Nil =>
        case List((p, _)) if p.ranges.isEmpty && isRenaming(instantiation(f.arity, ch.ctx, p), ch.order, p) =>
        case leaves =>
          val cases = leaves.flatMap((p, _) => expandRanges(p).map(_.map(caseText(f, _))).getOrElse(List(caseText(f, p) + " …")))
          reporter.report(ClauseProblem.InexactClause(f.name, cases, ch.state.source.span).toDiagnostic)

  /** A case of the tree with ranges on its variables ([[NatRange]]) as the cases without ranges that it
   *  stands for, as the unary tree would have them: a variable that cannot be the numerals of a set `E`
   *  is each allowed numeral below `max E + 1` and `Q + (max E + 1)` for a new variable `Q`; one below a
   *  bound is each allowed numeral below it. `None` if there would be more than [[MaxExpanded]]. */
  private def expandRanges(p: SplitProblem): Option[List[SplitProblem]] =
    p.ranges.keys.toList.sorted.find(p.isFree) match
      case None => Some(List(p.copy(ranges = Map.empty)))
      case Some(x) =>
        val r = p.range(x)
        val q = p.copy(ranges = p.ranges - x)
        val fam = natFamily(p.types(x))
        val top = r.below.getOrElse(r.excluded.maxOption.map(_ + 1).getOrElse(BigInt(0)))
        if top > MaxExpanded then None
        else
          val values = (BigInt(0) until top).filter(r.allows).map(v => q.solve(core, x, Val.Nat(fam, v))).toList
          val rest =
            if r.below.isDefined || top == 0 then Nil
            else
              val q1 = q.extend(q.names(x), q.types(x))
              List(q1.solve(core, x, natSuccs(natLike(fam).get._2, Val.local(q.size), top)))
          val cases = (values ++ rest).filterNot(_.dead)
          if cases.length > MaxExpanded then None
          else
            val expanded = cases.map(expandRanges)
            if expanded.contains(None) then None
            else
              val all = expanded.flatten.flatten
              Option.when(all.length <= MaxExpanded)(all)

  private val MaxExpanded = 20

  /** The leaves of a clause with their ranges expanded ([[expandRanges]]), each with the clause's state in
   *  it; `None` if there would be too many. */
  private def expandedLeaves(leaves: List[(SplitProblem, ClauseState)]): Option[List[(SplitProblem, ClauseState)]] =
    val expanded = leaves.map((p, cl) =>
      expandRanges(p).map(_.flatMap(q =>
        simplify(q, cl) match
          case Simplified.Ready(c) => Some((q, c))
          case _ => None
      ))
    )
    Option.when(!expanded.contains(None))(expanded.flatten.flatten)

  /** A case of the tree as a left-hand side of `f`, with `_` for its variables. */
  private def caseText(f: FunctionInfo, p: SplitProblem): String =
    val names = p.names.indices.map(l => if p.isFree(l) then "_" else p.names(l)).toList.reverse
    val pats = f.explicit.drop(globals(f.id).hidden).map(l => showTm(names, explicitOnly(quote(p.size, p.values(l)))))
    (f.name :: pats.map(s => if s.contains(' ') then s"($s)" else s)).mkString(" ")

object Clauses:
  /** For tests: `canApply` also unifies where it decided without unifying; `decidedWithoutUnifying` counts those
   *  decisions and `mismatches` collects the constructors where unification disagreed. */
  @volatile var crossCheck: Boolean = false
  val decidedWithoutUnifying: java.util.concurrent.atomic.AtomicLong = java.util.concurrent.atomic.AtomicLong()
  val mismatches: java.util.concurrent.ConcurrentLinkedQueue[String] = java.util.concurrent.ConcurrentLinkedQueue()
