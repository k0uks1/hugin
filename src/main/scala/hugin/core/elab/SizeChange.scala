package hugin.core
package elab

import hugin.util.*
import scala.collection.mutable

/** Termination of meta functions (REDESIGN §6.5) by the size-change principle (Lee, Jones & Ben-Amram,
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
  private final case class Call(caller: Int, callee: Int, m: Vector[Vector[Option[Rel]]], span: Span, shown: () => String)

  private val calls = mutable.ListBuffer.empty[Call]

  /** Records the calls of functions in the right-hand side `body` (elaborated in `c`) of a leaf of `f`. */
  def recordCalls(f: Clauses#FunctionInfo, callerArgs: Vector[Val], c: Cxt, body: Tm, source: SurfaceClause): Unit =
    def visit(t: Tm, env: List[Val], lvl: Int): Unit =
      val (head, args) = spine(t)
      calleeOf(head, env).foreach { (g, applied) =>
        val argVals = applied ++ args.map(a => eval(env, a))
        calls += Call(f.id, g, matrix(callerArgs, argVals, lvl, arity(g)), source.span, () => showTm(c.names, t))
      }
      args.foreach(visit(_, env, lvl))
      head match
        case Tm.Lam(_, _, b) => visit(b, Val.local(lvl) :: env, lvl + 1)
        case Tm.Pi(_, _, a, b) => visit(a, env, lvl); visit(b, Val.local(lvl) :: env, lvl + 1)
        case Tm.Let(_, _, d, b) => visit(d, env, lvl); visit(b, eval(env, d) :: env, lvl + 1)
        case Tm.App(_, _, _) | Tm.Global(_) | Tm.Var(_) => ()
        case other => Tm.children(other).foreach(visit(_, env, lvl))
    visit(body, c.env, c.lvl)

  /** The function a call head denotes, with the arguments it is already applied to: a function, or a
   *  variable bound to a partially applied one (a lifted local function of a `where` block). */
  private def calleeOf(head: Tm, env: List[Val]): Option[(Int, List[Val])] = head match
    case Tm.Global(g) if isFunction(g) => Some((g, Nil))
    case Tm.Var(ix) =>
      env(ix) match
        case Val.Rigid(Head.Glob(g), sp) if isFunction(g) => Some((g, sp.reverse.collect { case Elim.EApp(a, _) => a }))
        case _ => None
    case _ => None

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
    val bad = closure(cyclic).collect {
      case (f, g, m) if f == g && compose(m, m) == m && !m.indices.exists(i => m(i)(i).contains(Rel.Lt)) => f
    }.distinct
    for f <- bad if rejected.add(f) do
      globals(f).kind = GlobalKind.Function(arity(f), None)
      val call = calls.find(c => c.caller == f && c.callee == f).orElse(calls.find(_.caller == f))
      reporter.report(ClauseProblem.NotTerminating(globals(f).name, globals(f).span, call.map(c => (c.span, c.shown()))).toDiagnostic)

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
