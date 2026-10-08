package hugin.core

import scala.collection.mutable

/** Universe level variables and constraints `a ≤ b` between levels `v + k` (difference constraints).
 *
 *  Levels are inferred (reference: meta/universes; redesign question Q1): every `Type` written by the user gets a fresh level variable,
 *  cumulativity and formation rules add constraints, and the constraints must have a solution in the
 *  natural numbers. The set is kept consistent incrementally: [[le]] adds a constraint only if the result
 *  still has a solution (no cycle of positive weight, no level forced above an upper bound), and the
 *  current *least* solution is maintained (an incremental longest-path computation from the zero node).
 *  Level variables are global to an elaboration (no universe polymorphism; see docs/NOTES.md).
 */
final class Levels:
  /** Node 0 is the constant 0; node `v` (v ≥ 1) is the level variable `v`. */
  private val sol = mutable.ArrayBuffer(0)
  private val out = mutable.ArrayBuffer(List.empty[(Int, Int)])

  def fresh(): Level =
    sol += 0
    out += Nil
    Level(sol.length - 1, 0)

  // ------------------------------------------------------------------ backtracking

  /** The writes made since the oldest open [[checkpoint]], to undo them ([[rollback]]): the node and its
   *  value and edges before the write. A trail (as in Prolog's WAM, and Lean 4's restorable meta context)
   *  makes backtracking cost the changes made, where a snapshot of the whole graph costs its size. */
  private final class Write(val node: Int, val sol: Int, val out: List[(Int, Int)])
  private val trail = mutable.ArrayBuffer.empty[Write]
  private var open = 0

  /** Opens a checkpoint; it must be closed by [[rollback]] or [[commit]], innermost first. */
  def checkpoint(): Levels.Checkpoint =
    open += 1
    Levels.Checkpoint(sol.length, trail.length)

  /** Returns to the state at `c` and closes it. */
  def rollback(c: Levels.Checkpoint): Unit =
    while trail.length > c.at do
      val w = trail.remove(trail.length - 1)
      sol(w.node) = w.sol
      out(w.node) = w.out
    sol.dropRightInPlace(sol.length - c.nodes)
    out.dropRightInPlace(out.length - c.nodes)
    commit(c)

  /** Closes `c`, keeping the changes since (an enclosing checkpoint can still undo them). */
  def commit(c: Levels.Checkpoint): Unit =
    open -= 1
    if open == 0 then trail.clear()

  private def write(n: Int, value: Int, edges: List[(Int, Int)]): Unit =
    if open > 0 then trail += Write(n, sol(n), out(n))
    sol(n) = value
    out(n) = edges

  /** The value of a level in the current least solution. */
  def value(l: Level): Int = if l.isConst then l.k else sol(l.v) + l.k

  private def node(l: Level): Int = if l.isConst then 0 else l.v

  /** Adds `a ≤ b`; returns false (and adds nothing) if the constraints would become unsatisfiable. */
  def le(a: Level, b: Level): Boolean =
    // node(b) ≥ node(a) + (a.k - b.k)
    addEdge(node(a), node(b), a.k - b.k)

  def eq(a: Level, b: Level): Boolean =
    val saved = checkpoint()
    if le(a, b) && le(b, a) then
      commit(saved)
      true
    else
      rollback(saved)
      false

  /** `a < b`. */
  def lt(a: Level, b: Level): Boolean = le(a.succ, b)

  /** The number of level variables (and the constant node). */
  def count: Int = sol.length

  /** A copy (for a fork of the core). */
  def copy(): Levels =
    val l = Levels()
    l.restore(snapshot())
    l

  /** The whole state (for tests). */
  def snapshot(): (Vector[Int], Vector[List[(Int, Int)]]) = (sol.toVector, out.toVector)
  private def restore(s: (Vector[Int], Vector[List[(Int, Int)]])): Unit =
    sol.clear(); sol ++= s._1
    out.clear(); out ++= s._2

  private def addEdge(u: Int, w: Int, c: Int): Boolean =
    if u == w then c <= 0
    else
      val changed = mutable.HashMap.empty[Int, Int]
      def bump(n: Int, v: Int): Unit =
        if !changed.contains(n) then changed(n) = sol(n)
        write(n, v, out(n))
      var ok = true
      if sol(w) < sol(u) + c then
        if w == 0 then ok = false
        else
          bump(w, sol(u) + c)
          val work = mutable.Queue(w)
          while ok && work.nonEmpty do
            val n = work.dequeue()
            for (m, d) <- out(n) if ok && sol(m) < sol(n) + d do
              if m == u || m == 0 then ok = false
              else
                bump(m, sol(n) + d)
                work.enqueue(m)
      if ok then
        write(u, sol(u), (w, c) :: out(u))
        true
      else
        for (n, v) <- changed do write(n, v, out(n))
        false

object Levels:
  /** A state to return to ([[Levels.checkpoint]]): the number of nodes and the length of the trail. */
  final class Checkpoint private[Levels] (private[Levels] val nodes: Int, private[Levels] val at: Int)
