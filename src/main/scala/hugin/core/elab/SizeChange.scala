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
   *  argument `j` of the callee). */
  private final case class Call(caller: Int, callee: Int, m: Vector[Vector[Option[Rel]]], span: Span, shown: String)

  private val calls = mutable.ListBuffer.empty[Call]

  /** Records the calls of functions in the right-hand side `body` (elaborated in `c`) of a leaf of `f`. */
  def recordCalls(f: Clauses#FunctionInfo, callerArgs: Vector[Val], c: Cxt, body: Tm, source: SurfaceClause): Unit =
    def visit(t: Tm, env: List[Val], lvl: Int): Unit =
      val (head, args) = spine(t)
      calleeOf(head, env).foreach { (g, applied) =>
        val argVals = applied ++ args.map(a => eval(env, a))
        calls += Call(f.id, g, matrix(callerArgs, argVals, lvl, arity(g)), source.span, showTm(c.names, t))
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

  private type Graph = (Int, Int, Vector[Vector[Option[Rel]]])

  private def compose(a: Vector[Vector[Option[Rel]]], b: Vector[Vector[Option[Rel]]]): Vector[Vector[Option[Rel]]] =
    val k = b.headOption.map(_.length).getOrElse(0)
    a.map { row =>
      (0 until k).map { j =>
        row.indices.flatMap { m =>
          (row(m), b.lift(m).flatMap(_.lift(j)).flatten) match
            case (Some(x), Some(y)) => Some(if x == Rel.Lt || y == Rel.Lt then Rel.Lt else Rel.Le)
            case _ => None
        }.maxByOption(r => if r == Rel.Lt then 1 else 0)
      }.toVector
    }

  private val rejected = mutable.Set.empty[Int]

  /** Checks the calls recorded so far; reports E0912 for each function that may not terminate (once) and
   *  removes its case tree, so that it never reduces. Run after each function's case tree is installed,
   *  before anything can evaluate it: a function only reduces once its call cycles are known to
   *  terminate (cycles through functions elaborated later are stuck until those are checked). */
  def checkTermination(): Unit =
    val base = calls.toList
    // only calls inside a strongly connected component of the call graph can be on a cycle
    val nodes = base.flatMap(c => List(c.caller, c.callee)).distinct
    val succ = base.groupMap(_.caller)(_.callee)
    val component = Graphs.components(nodes, n => succ.getOrElse(n, Nil)).zipWithIndex.flatMap((c, i) => c.map(_ -> i)).toMap
    val cyclic = base.filter(c => component(c.caller) == component(c.callee))
    val closure = mutable.LinkedHashSet.from(cyclic.map(c => (c.caller, c.callee, c.m): Graph))
    var frontier = closure.toList
    while frontier.nonEmpty do
      val next =
        for
          (f, g, a) <- frontier
          (g2, h, b) <- closure.toList if g2 == g
          composed = (f, h, compose(a, b))
          if !closure.contains(composed)
        yield composed
      closure ++= next
      frontier = next.distinct
    val bad = closure.toList.collect {
      case (f, g, m) if f == g && compose(m, m) == m && !m.indices.exists(i => m(i)(i).contains(Rel.Lt)) => f
    }.distinct
    for f <- bad if rejected.add(f) do
      globals(f).kind = GlobalKind.Function(arity(f), None)
      val call = base.find(c => c.caller == f && c.callee == f).orElse(base.find(_.caller == f))
      reporter.report(ClauseProblem.NotTerminating(globals(f).name, globals(f).span, call.map(c => (c.span, c.shown))).toDiagnostic)
