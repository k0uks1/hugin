package hugin.core
package elab

import hugin.util.*
import hugin.util.diagnostics.{Applicability, Edit, Suggestion}
import scala.collection.mutable

/** Termination of meta functions (reference: meta/coverage) by the size-change principle (Lee, Jones & Ben-Amram,
 *  POPL 2001) over the constructor-subterm order:
 *
 *  - every call `g ā` in the right-hand side of a clause of `f` gives a size-change graph from `f`'s
 *    arguments (the clause's patterns, as terms of the leaf) to `g`'s: `i ↓ j` if `a_j` is a proper
 *    constructor subterm of argument `i`, `i ⇊= j` if it is equal;
 *  - the graphs are closed under composition along the call graph; the functions terminate if every
 *    idempotent graph `f → f` of the closure has a strict arc `i ↓ i`.
 *
 *  This covers structural recursion, mutual recursion, lexicographic orders and permuted arguments. Calls
 *  in which a function is not applied (passed as a value) are calls with unknown arguments. */
trait SizeChange:
  self: Elaborator =>
  import core.*

  private enum Rel:
    case Le, Lt

  /** A call `caller → callee` with its size-change matrix (`m(i)(j)`: argument `i` of the caller to
   *  argument `j` of the callee); `shown` prints it for a diagnostic (only then: printing is pure). */
  private final case class Call(caller: Int, callee: Int, m: Vector[Vector[Option[Rel]]], span: Span, shown: () => String, clause: Int)

  private val calls = mutable.ListBuffer.empty[Call]

  /** The number of calls recorded so far. */
  def callCount: Int = calls.length

  /** The calls of a clause at the leaves of its function's case tree, where they refine its clause
   *  context, and the clause written out at those leaves (reference: meta/clauses, "Checking a clause"). */
  private final case class Alternative(calls: List[Call], text: String, span: Span)

  /** The alternatives by function and clause. */
  private val alternatives = mutable.HashMap.empty[(Int, Int), Alternative]

  /** Records the calls of clause `clause` of `f` at the leaves that refine its clause context: each visit
   *  is the caller's arguments at a leaf, a context for display, the environment of the context at the
   *  leaf, the level of the leaf's variables and a term of the clause. If the termination check rejects
   *  `f` but these calls make it terminate, its error has a fix that replaces the clause by `text`. */
  def recordAlternative(
      f: Clauses#FunctionInfo,
      clause: Int,
      visits: List[(Vector[Val], Cxt, List[Val], Int, Tm)],
      source: SurfaceClause,
      text: String
  ): Unit =
    val out = mutable.ListBuffer.empty[Call]
    for (args, c, env, lvl, t) <- visits do CallCollector(f.id, args, c, source.span, clause, out).visit(t, env, lvl, Nil, None)
    alternatives((f.id, clause)) = Alternative(out.toList, text, source.span)

  /** Records the calls of functions in the right-hand side `body` (elaborated in `c`) of a leaf of `f`.
   *
   *  A call can be hidden behind another name, and evaluation finds it there; so the calls are collected
   *  where evaluation would find them (reference: meta/termination):
   *
   *  - a definition applied to arguments is inlined: its term is visited with the argument values for its
   *    parameters, so `g = [x] f x` makes `g (suc N)` the call `f (suc N)`; this also covers
   *    definitions in definitions and partial applications stored in definitions (`h = f`, `h = k zero`);
   *  - a field of a record term (`ops.step` with `ops = { step = [x] f x }`, also through definitions)
   *    is visited as that field's term applied to the arguments;
   *  - a variable bound to a closure, a record or a partial application (a `let`, a lifted local
   *    function of a `where` block, an inlined parameter) is followed through its value, as is the
   *    solution of a meta (an implicit argument);
   *  - what cannot be followed with its arguments is a call with unknown arguments to every function it
   *    may reach: a definition or lambda that is not applied, and module bodies (functor applications,
   *    whose members and items see the body's parameters).
   *
   *  Definitions are not recursive (E0105), so inlining terminates. */
  def recordCalls(f: Clauses#FunctionInfo, callerArgs: Vector[Val], c: Cxt, body: Tm, source: SurfaceClause, clause: Int): Unit =
    CallCollector(f.id, callerArgs, c, source.span, clause, calls).visit(body, c.env, c.lvl, Nil, None)

  /** The calls of one right-hand side; `site` is the term of the clause (in the clause's context) that
   *  a call shows in a diagnostic, `None` while visiting the clause's own syntax. */
  private final class CallCollector(caller: Int, callerArgs: Vector[Val], c: Cxt, span: Span, clause: Int, out: mutable.ListBuffer[Call]):
    private var depth = 0
    private var steps = 0
    private val unknownDone = mutable.HashSet.empty[Int]

    private def record(g: Int, args: List[Val], lvl: Int, site: Tm): Unit =
      out += Call(caller, g, matrix(callerArgs, args, lvl, arity(g)), span, () => showTm(c.names, zonk(c.env, c.lvl, site)), clause)

    /** `t` (in `env`, under `lvl` binders) applied to the further arguments `extra`. */
    def visit(t: Tm, env: List[Val], lvl: Int, extra: List[Val], site0: Option[Tm]): Unit =
      val site = site0.getOrElse(t)
      val (head, args) = spine(t)
      lazy val argVals = args.map(a => eval(env, a)) ++ extra
      args.foreach(a => visit(a, env, lvl, Nil, site0))
      head match
        case Tm.Global(g) if isFunction(g) => record(g, argVals, lvl, site)
        case Tm.Global(g) =>
          definitionTerm(g).foreach(d => inlining(g, lvl, site)(visitApplied(d, Nil, lvl, argVals, site)))
        case Tm.Var(ix) => env.lift(ix).foreach(v => visitValue(v, lvl, argVals, site, deep = false))
        case Tm.Meta(m) => metas(m).solution.foreach(v => visitValue(v, lvl, argVals, site, deep = true))
        case Tm.AppPruning(Tm.Meta(m), pr) =>
          val selected = env.zip(pr).reverse.collect { case (v, Some(_)) => v }
          metas(m).solution.foreach(v => visitValue(v, lvl, selected ++ argVals, site, deep = true))
        case Tm.Proj(a, l) =>
          field(a, env, l) match
            case Some(Left((ft, fenv))) => visitApplied(ft, fenv, lvl, argVals, site)
            case Some(Right(v)) => visitValue(v, lvl, argVals, site, deep = false)
            case None => visit(a, env, lvl, Nil, site0)
        case Tm.Lam(_, _, _) => visitApplied(head, env, lvl, argVals, site)
        case Tm.Pi(_, _, a, b) =>
          visit(a, env, lvl, Nil, site0); visit(b, Val.local(lvl) :: env, lvl + 1, Nil, site0)
        case Tm.Let(_, _, d, b) =>
          visit(d, env, lvl, Nil, site0); visit(b, eval(env, d) :: env, lvl + 1, argVals, site0)
        case Tm.Module(b, menv) =>
          menv.foreach(visit(_, env, lvl, Nil, site0))
          moduleFunctions(b).foreach(g => unknown(g, lvl, site))
        case Tm.RecTy(fs, _, _) =>
          var e = env
          var lv = lvl
          for (_, ty) <- fs do
            visit(ty, e, lv, Nil, site0)
            e = Val.local(lv) :: e
            lv += 1
        case Tm.Fresh(ns, b) =>
          val locals = ns.indices.map(i => Val.local(lvl + i)).reverse.toList
          visit(b, locals ++ env, lvl + ns.length, Nil, site0)
        case Tm.App(_, _, _) => ()
        case other => Tm.children(other).foreach(visit(_, env, lvl, Nil, site0))

    /** The term `t` (in `env`) applied to `args`: its lambdas take the arguments; lambdas without one
     *  bind unknown values. */
    private def visitApplied(t: Tm, env: List[Val], lvl: Int, args: List[Val], site: Tm): Unit = (t, args) match
      case (Tm.Lam(_, _, b), a :: rest) => visitApplied(b, a :: env, lvl, rest, site)
      case (Tm.Lam(_, _, b), Nil) => visitApplied(b, Val.local(lvl) :: env, lvl + 1, Nil, site)
      case _ => visit(t, env, lvl, args, Some(site))

    /** A value applied to `args`, followed without evaluating it: a closure by its term, a neutral
     *  application of a function as a call, of a definition by inlining. The value of a variable
     *  (`deep = false`) came from syntax that is visited where it is written, so only its head is
     *  followed; a meta's solution (`deep = true`) is visited through all its parts. */
    private def visitValue(v: Val, lvl: Int, args: List[Val], site: Tm, deep: Boolean): Unit =
      def part(x: Val) = if deep then visitValue(x, lvl, Nil, site, deep) else ()
      def closure(b: Tm, env: List[Val]) = if deep then visit(b, Val.local(lvl) :: env, lvl + 1, Nil, Some(site)) else ()
      v match
        case Val.Lam(_, _, cl) =>
          if args.nonEmpty || deep then visitApplied(Tm.Lam("_", Icit.Expl, cl.body), cl.env, lvl, args, site)
        case Val.Top(g, sp, u) =>
          // a folded definition: inlined with its arguments, as a definition written in the syntax
          if sp.forall(_.isInstanceOf[Elim.EApp]) then
            val spArgs = sp.reverse.collect { case Elim.EApp(a, _) => a }
            spArgs.foreach(part)
            definitionTerm(g).foreach(d => inlining(g, lvl, site)(visitApplied(d, Nil, lvl, spArgs ++ args, site)))
          else visitValue(u.value, lvl, args, site, deep)
        case Val.Rigid(h, sp) =>
          val spArgs = sp.reverse.collect { case Elim.EApp(a, _) => a }
          spArgs.foreach(part)
          h match
            case Head.Glob(g) if isFunction(g) =>
              if sp.forall(_.isInstanceOf[Elim.EApp]) then record(g, spArgs ++ args, lvl, site) else unknown(g, lvl, site)
            case Head.Glob(g) =>
              definitionTerm(g).foreach(d => inlining(g, lvl, site)(visitApplied(d, Nil, lvl, spArgs ++ args, site)))
            case Head.Module(b, env) =>
              env.foreach(part)
              moduleFunctions(b).foreach(g => unknown(g, lvl, site))
            case Head.Local(_) => ()
        case Val.Flex(m, sp) =>
          val spArgs = sp.reverse.collect { case Elim.EApp(a, _) => a }
          spArgs.foreach(part)
          metas(m).solution.foreach(s => visitValue(s, lvl, spArgs ++ args, site, deep = true))
        case Val.Obj(ObjForm.Loc(_), List(x)) => visitValue(x, lvl, args, site, deep)
        case Val.Pi(_, _, a, cl) => part(a); closure(cl.body, cl.env)
        case Val.Rec(fs) => fs.foreach(x => part(x._2))
        case Val.RecTy(_, env, tys, _, _) if deep =>
          var e = env
          var lv = lvl
          for ty <- tys do
            visit(ty, e, lv, Nil, Some(site))
            e = Val.local(lv) :: e
            lv += 1
        case Val.Lift(a) => part(a)
        case Val.Quote(a) => part(a)
        case Val.Persist(a) => part(a)
        case Val.FactTy(a) => part(a)
        case Val.Arith(_, a, b, _) => part(a); part(b)
        case Val.Negate(a, _) => part(a)
        case Val.Obj(_, as) => as.foreach(part)
        case _ => ()

    /** The field `l` of the record that `a` denotes, if it is a record term (through definitions) or a
     *  record value: the field's term with its environment, or its value. */
    private def field(a: Tm, env: List[Val], l: Name): Option[Either[(Tm, List[Val]), Val]] = a match
      case Tm.Rec(fs) => fs.find(_._1 == l).map(x => Left((x._2, env)))
      case Tm.Global(g) => definitionTerm(g).flatMap(field(_, Nil, l))
      case Tm.Var(ix) =>
        env.lift(ix) match
          case Some(Val.Rec(fs)) => fs.find(_._1 == l).map(x => Right(x._2))
          case _ => None
      case Tm.Proj(b, l2) =>
        field(b, env, l2) match
          case Some(Left((t, fenv))) => field(t, fenv, l)
          case Some(Right(Val.Rec(fs))) => fs.find(_._1 == l).map(x => Right(x._2))
          case _ => None
      case Tm.Module(b, menv) => member(b, menv.map(eval(env, _)), l)
      case Tm.Trace(_, t) => field(t, env, l)
      case Tm.Require(_, _, t) => field(t, env, l)
      case Tm.App(_, _, _) =>
        // a functor applied to all its parameters: the field of its body
        val (h, args) = spine(a)
        h match
          case Tm.Global(g) =>
            definitionTerm(g).flatMap { d =>
              var t = d
              var e = List.empty[Val]
              var rest = args
              while rest.nonEmpty && t.isInstanceOf[Tm.Lam] do
                e = eval(env, rest.head) :: e
                rest = rest.tail
                t = t.asInstanceOf[Tm.Lam].body
              if rest.isEmpty && !t.isInstanceOf[Tm.Lam] then field(t, e, l) else None
            }
          case _ => None
      case _ => None

    /** The member `l` of a module body in the environment `menv`: its definition, in the environment of
     *  the members before it (their values, object members as placeholders). `None` (calls with
     *  unknown arguments) for an object member, or if an earlier member's definition would instantiate a
     *  module or create object variables when evaluated. */
    private def member(b: ModuleBody, menv: List[Val], l: Name): Option[Either[(Tm, List[Val]), Val]] =
      var e = menv
      var result: Option[Either[(Tm, List[Val]), Val]] = None
      var ok = true
      val it = b.members.iterator
      while ok && result.isEmpty && it.hasNext do
        val m = it.next()
        m.kind match
          case MemberKind.Defined(t) if m.name == l => result = Some(Left((t, e)))
          case MemberKind.Defined(t) if pure(t) => e = eval(e, t) :: e
          case MemberKind.Object(_) if m.name != l => e = Val.Wild :: e
          case _ => ok = false
      result

    /** Evaluating `t` has no effect: it instantiates no module body and creates no object variable. */
    private def pure(t: Tm): Boolean = !Tm.exists(t) {
      case Tm.Module(_, _) | Tm.Fresh(_, _) => true
      case _ => false
    }

    /** Runs `k` (inlining definition `g`) unless the inlining is too deep, in which case the functions
     *  `g` may reach are called with unknown arguments. */
    private def inlining(g: Int, lvl: Int, site: Tm)(k: => Unit): Unit =
      steps += 1
      if depth >= MaxInlining || steps > MaxInlineSteps then reachableFunctions(g).foreach(h => unknown(h, lvl, site))
      else
        depth += 1
        try k
        finally depth -= 1

    /** A call of `g` with arguments that are not known (all arcs absent), once per right-hand side. */
    private def unknown(g: Int, lvl: Int, site: Tm): Unit =
      if unknownDone.add(g) then record(g, Nil, lvl, site)

  /** Bounds on inlining per right-hand side (nesting, and inlined definitions in all); beyond them the
   *  calls a definition may reach have unknown arguments. */
  private val MaxInlining = 64
  private val MaxInlineSteps = 10000

  /** The term of a definition. */
  private def definitionTerm(g: Int): Option[Tm] = kindOf(g) match
    case GlobalKind.Definition(tm, _) => Some(tm)
    case _ => None

  private val reachableMemo = mutable.HashMap.empty[Int, Set[Int]]

  /** The functions that the term of definition `g` refers to, also through the definitions, module
   *  bodies and solved metas it refers to. */
  private def reachableFunctions(g: Int): Set[Int] =
    reachableMemo.get(g) match
      case Some(r) => r
      case None =>
        reachableMemo(g) = Set.empty // definitions are not recursive; guards a malformed cycle
        val r = definitionTerm(g).map(functionsIn).getOrElse(Set.empty)
        reachableMemo(g) = r
        r

  private def functionsIn(t: Tm): Set[Int] = t match
    case Tm.Global(g) if isFunction(g) => Set(g)
    case Tm.Global(g) => reachableFunctions(g)
    case Tm.Meta(m) => metas(m).solution.map(functionsInVal(_, 0)).getOrElse(Set.empty)
    case Tm.Module(b, env) => env.flatMap(functionsIn).toSet ++ moduleFunctions(b)
    case other => Tm.children(other).flatMap(functionsIn).toSet

  private def functionsInVal(v: Val, depth: Int): Set[Int] =
    if depth > MaxInlining then Set.empty
    else
      def sp(s: Spine) = s.collect { case Elim.EApp(a, _) => functionsInVal(a, depth + 1) }.flatten.toSet
      v match
        case Val.Lam(_, _, cl) => functionsIn(cl.body) ++ cl.env.flatMap(functionsInVal(_, depth + 1))
        case Val.Pi(_, _, a, cl) => functionsInVal(a, depth + 1) ++ functionsIn(cl.body)
        case Val.Rigid(Head.Glob(g), s) => (if isFunction(g) then Set(g) else reachableFunctions(g)) ++ sp(s)
        case Val.Top(g, s, _) => reachableFunctions(g) ++ sp(s)
        case Val.Rigid(Head.Module(b, env), s) => moduleFunctions(b) ++ env.flatMap(functionsInVal(_, depth + 1)) ++ sp(s)
        case Val.Rigid(_, s) => sp(s)
        case Val.Flex(m, s) => metas(m).solution.map(functionsInVal(_, depth + 1)).getOrElse(Set.empty) ++ sp(s)
        case Val.Rec(fs) => fs.flatMap(x => functionsInVal(x._2, depth + 1)).toSet
        case Val.Lift(a) => functionsInVal(a, depth + 1)
        case Val.Quote(a) => functionsInVal(a, depth + 1)
        case Val.Persist(a) => functionsInVal(a, depth + 1)
        case Val.Obj(_, as) => as.flatMap(functionsInVal(_, depth + 1)).toSet
        case _ => Set.empty

  private val moduleMemo = mutable.HashMap.empty[Int, Set[Int]]

  /** The functions a module body refers to in its members and items. */
  private def moduleFunctions(b: ModuleBody): Set[Int] =
    moduleMemo.getOrElseUpdate(
      b.id,
      b.members.flatMap { m =>
        functionsIn(m.ty) ++ (m.kind match
          case MemberKind.Defined(t) => functionsIn(t)
          case MemberKind.Object(_) => Set.empty
        )
      }.toSet ++ b.items.flatMap(CoreItem.terms).flatMap(functionsIn)
    )

  private def isFunction(g: Int): Boolean = globals(g).kind.isInstanceOf[GlobalKind.Function]

  private def arity(g: Int): Int = globals(g).kind match
    case GlobalKind.Function(a, _) if a >= 0 => a
    case _ => telescope(globals(g).ty)._1.length

  private def spine(t: Tm): (Tm, List[Tm]) = t match
    case Tm.App(f, a, _) =>
      val (h, as) = spine(f)
      (h, as :+ a)
    case other => (other, Nil)

  private def matrix(callerArgs: Vector[Val], calleeArgs: List[Val], lvl: Int, calleeArity: Int): Vector[Vector[Option[Rel]]] =
    val callee = calleeArgs.take(calleeArity).map(quote(lvl, _)).toVector
    callerArgs.map { a =>
      val q = quote(lvl, a)
      (0 until calleeArity).map(j => callee.lift(j).flatMap(compare(q, _))).toVector
    }

  /** How the callee's argument `b` relates to the caller's argument `a`. */
  private def compare(a: Tm, b: Tm): Option[Rel] =
    if a == b then Some(Rel.Le) else Option.when(properSubterm(b, a))(Rel.Lt)

  /** `b` is a proper subterm of the constructor term `a`. */
  private def properSubterm(b: Tm, a: Tm): Boolean =
    val (h, args) = spine(a)
    h match
      case Tm.Global(c) if isConstructor(c) => args.exists(x => x == b || properSubterm(b, x))
      case _ => false

  // ---------------------------------------------------------------- the size-change principle

  private type Matrix = Vector[Vector[Option[Rel]]]
  private type Graph = (Int, Int, Matrix)

  private val someLt: Option[Rel] = Some(Rel.Lt)
  private val someLe: Option[Rel] = Some(Rel.Le)

  /** The graph of a call to `b`'s caller followed by `b`: an arc `i → j` through some `m`, strict if one
   *  of the two arcs is (the strongest such arc). */
  private def compose(a: Matrix, b: Matrix): Matrix =
    val k = b.headOption.map(_.length).getOrElse(0)
    a.map { row =>
      Vector.tabulate(k) { j =>
        var best: Option[Rel] = None
        var m = 0
        while m < row.length && !best.contains(Rel.Lt) do
          row(m) match
            case Some(x) if m < b.length && j < b(m).length =>
              b(m)(j) match
                case Some(y) => best = if x == Rel.Lt || y == Rel.Lt then someLt else someLe
                case None =>
            case _ =>
          m += 1
        best
      }
    }

  private val rejected = mutable.Set.empty[Int]

  /** Whether the function `f` was rejected by the termination check (E0912): it never reduces. */
  def rejectedByTermination(f: Int): Boolean = rejected(f)

  /** The number of recorded calls already checked by [[checkTermination]]. */
  private var checkedCalls = 0

  /** The call graph of the checked calls: callees and callers of each function. */
  private val callees = mutable.HashMap.empty[Int, mutable.Set[Int]]
  private val callers = mutable.HashMap.empty[Int, mutable.Set[Int]]

  /** Checks the calls recorded so far; reports E0912 for each function that may not terminate (once) and
   *  removes its case tree, so that it never reduces. Run after each function's case tree is installed,
   *  before anything can evaluate it: a function only reduces once its call cycles are known to
   *  terminate (cycles through functions elaborated later are stuck until those are checked).
   *
   *  Only calls inside a strongly connected component of the call graph can be on a cycle, and the
   *  verdict for a component depends only on the calls inside it (Agda's termination checker also works
   *  per component). Calls are only ever added, so a component without a call recorded since the last
   *  check has exactly the calls it had then (a component that grew, by merging, contains the new call
   *  that merged it): its verdict is the one already acted on, and only the components with new calls
   *  inside them are checked again. The component of a new call's caller is the set of functions it
   *  reaches that reach it back. */
  def checkTermination(): Unit =
    val fresh = calls.view.drop(checkedCalls).toList
    checkedCalls = calls.length
    for c <- fresh do
      callees.getOrElseUpdate(c.caller, mutable.LinkedHashSet.empty) += c.callee
      callers.getOrElseUpdate(c.callee, mutable.LinkedHashSet.empty) += c.caller
    val components = mutable.ArrayBuffer.empty[collection.Set[Int]]
    for c <- fresh if !components.exists(k => k(c.caller) && k(c.callee)) do
      val component = reachable(c.caller, callees).intersect(reachable(c.caller, callers))
      if component(c.callee) then components += component
    if components.isEmpty then return
    val cyclic = calls.toList.filter(c => components.exists(k => k(c.caller) && k(c.callee)))
    val bad = nonTerminating(cyclic)
    for f <- bad if rejected.add(f) do
      globals(f).kind = GlobalKind.Function(arity(f), None)
      val call = calls.find(c => c.caller == f && c.callee == f).orElse(calls.find(_.caller == f))
      val d = ClauseProblem.NotTerminating(globals(f).name, globals(f).span, call.map(c => (c.span, c.shown()))).toDiagnostic
      reporter.report(refinementFix(f, cyclic, components).fold(d)(s => d.copy(suggestions = d.suggestions :+ s)))

  /** The functions with an idempotent size-change graph `f → f` without a strict arc on its diagonal. */
  private def nonTerminating(cyclic: List[Call]): List[Int] =
    closure(cyclic).collect {
      case (f, g, m) if f == g && compose(m, m) == m && !m.indices.exists(i => m(i)(i).contains(Rel.Lt)) => f
    }.distinct

  /** A fix for the rejection of `f`: the clauses of its components written out at their leaves, if their
   *  calls there ([[recordAlternative]]) make `f` terminate (a call that decreases only through the
   *  refinement made by earlier clauses, `h N M = h (predf N) M` after `h zero _ = zero`). */
  private def refinementFix(f: Int, cyclic: List[Call], components: collection.Seq[collection.Set[Int]]): Option[Suggestion] =
    def inComponent(c: Call) = components.exists(k => k(c.caller) && k(c.callee))
    val used = alternatives.filter((key, _) => cyclic.exists(c => (c.caller, c.clause) == key))
    if used.isEmpty then None
    else
      val replaced = cyclic.filterNot(c => used.contains((c.caller, c.clause))) ++ used.values.flatMap(_.calls).filter(inComponent)
      if nonTerminating(replaced).contains(f) then None
      else
        val edits = used.values.toList.sortBy(_.span.start).map(a => Edit(a.span, a.text))
        val shown = edits.map(e => s"`${e.replacement.linesIterator.map(_.trim).mkString(" ")}`").mkString(", ")
        Some(Suggestion(s"write out the cases of the clause: $shown", edits, Applicability.MachineApplicable))

  /** The functions reachable from `f` (itself included) along `edges`. */
  private def reachable(f: Int, edges: mutable.HashMap[Int, mutable.Set[Int]]): mutable.Set[Int] =
    val seen = mutable.HashSet(f)
    val todo = mutable.Stack(f)
    while todo.nonEmpty do
      for g <- edges.getOrElse(todo.pop(), Nil) if seen.add(g) do todo.push(g)
    seen

  /** The size-change graphs of all paths of calls: the calls closed under composition. A path is
   *  extended at its end by one call at a time, so each new graph is composed with the calls of its
   *  callee only. */
  private def closure(cyclic: List[Call]): List[Graph] =
    val result = mutable.LinkedHashSet.from(cyclic.map(c => (c.caller, c.callee, c.m): Graph))
    val from = cyclic.groupMap(_.caller)(c => (c.callee, c.m)).withDefaultValue(Nil)
    var frontier = result.toList
    while frontier.nonEmpty do
      val next = mutable.ListBuffer.empty[Graph]
      for (f, g, a) <- frontier; (h, b) <- from(g) do
        val composed = (f, h, compose(a, b))
        if result.add(composed) then next += composed
      frontier = next.toList
    result.toList
