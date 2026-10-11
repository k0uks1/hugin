package hugin.obj
package check

import scala.collection.mutable

import SizeChange.{Eq, Graph, Step, isDown, isUp, strict}

/** The size-change steps of a component restricted to the arguments that can carry a descent (found by
 *  the fuzzers, #150 and #67). Arguments that every step only carries along, permuting them by `=` arcs
 *  (seven in `t_termination_large_closure` without its reset rule), multiply the closure by their
 *  permutations (5040 graphs per parity of the fuel swap, pairwise incomparable, so the antichain of
 *  [[SizeChange.check]] keeps them all) but take no part in a descent. [[SizeChange.check]] first runs
 *  the closure of `steps` with the criterion `passes`; if that passes, so does the closure of all
 *  arguments. Otherwise the closure of all arguments decides and reports, as before.
 *
 *  `kept` are the arguments `(r, i)` that lie, in the graph of all arcs of the steps, on a cycle through
 *  a strict arc whose arcs all go in the strict arc's direction (`=` belongs to both); `steps` keep only
 *  the arcs between kept arguments. A descent is a thread in the sense of Lee, Jones and Ben-Amram (POPL
 *  2001): only the arguments a descending thread can pass are needed to find one.
 *
 *  *First alternative* of the local criterion ([[Graph.descendsStrictly]]): it holds for the graph of a
 *  chain iff it holds for the chain's projected graph. A strict cycle of the chain's graph is a cyclic
 *  thread of the chain repeated, in one direction through a strict arc, so every argument it passes, at
 *  every step, is kept, and the projected graph has the same paths, labels and cycle. Conversely the
 *  projected graph's arcs are paths of the full graph with their labels (a weak arc there may be implied
 *  by an `=` or strict arc of the same direction, which closes the same cycle).
 *
 *  *Second alternative* (every argument on an `=` cycle): it needs every argument, so in general a
 *  projected graph proves nothing by it, and `passes` is the first alternative alone. But if the steps
 *  are `separable` — no arc joins a kept and a left-out argument, and every step maps the left-out
 *  arguments of its premise one to one onto those of its conclusion by `=` arcs, with no other arcs
 *  among them — then the graph of a chain is its projected graph together with a permutation of the
 *  left-out arguments by `=` arcs, on which every argument lies on an `=` cycle. The second alternative
 *  then holds iff every *kept* argument lies on an `=` cycle of the projected graph, and `passes` is the
 *  whole local criterion over the kept arguments ([[Graph.descendsOn]]).
 *
 *  Either way `passes` holds for a chain's projected graph only if the local criterion holds for its
 *  graph, and `passes` is upward closed in [[Graph.weakerThan]] (a strict or `=` arc is implied only by
 *  an arc of its kind), so the antichain decides it for the whole projected closure as in
 *  [[SizeChange.check]]. */
final case class SizeChangeProjection(steps: Vector[Step], kept: Set[(RelSym, Int)], separable: Boolean):
  def passes(r: RelSym, g: Graph): Boolean =
    if separable then g.descendsOn((0 until r.arity).filter(i => kept((r, i)))) else g.descendsStrictly

object SizeChangeProjection:
  private type Node = (RelSym, Int)

  def apply(base: Vector[Step]): SizeChangeProjection =
    val arcs = base.flatMap(s => s.graph.arcs.iterator.map(a => ((s.from, a.from), (s.to, a.to), a.label)))
    def reach(start: Node, along: Int => Boolean, forward: Boolean): Set[Node] =
      val next = arcs.filter(a => along(a._3)).groupMap(a => if forward then a._1 else a._2)(a => if forward then a._2 else a._1)
      val seen = mutable.Set(start)
      val todo = mutable.Stack(start)
      while todo.nonEmpty do
        for n <- next.getOrElse(todo.pop(), Vector.empty) if seen.add(n) do todo.push(n)
      seen.toSet
    val kept: Set[Node] = arcs.iterator
      .filter(a => strict(a._3))
      .flatMap { (u, v, l) =>
        val along: Int => Boolean = if isDown(l) then k => k == Eq || isDown(k) else k => k == Eq || isUp(k)
        val after = reach(v, along, forward = true)
        if after(u) then after.intersect(reach(u, along, forward = false)) else Set.empty
      }
      .toSet
    val separable = base.forall { s =>
      val (inside, outside) = s.graph.arcs.partition(a => kept((s.from, a.from)))
      def left(r: RelSym) = (0 until r.arity).filterNot(i => kept((r, i))).toSet
      inside.forall(a => kept((s.to, a.to))) && outside.forall(a => a.label == Eq && !kept((s.to, a.to))) &&
      outside.size == left(s.from).size && outside.size == left(s.to).size && outside.map(_.from) == left(s.from) && outside.map(
        _.to
      ) == left(s.to)
    }
    val steps = base.map(s => s.copy(graph = Graph(s.graph.arcs.filter(a => kept((s.from, a.from)) && kept((s.to, a.to))))))
    SizeChangeProjection(steps, kept, separable)
