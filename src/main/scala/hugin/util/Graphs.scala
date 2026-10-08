package hugin.util

import org.jgrapht.alg.shortestpath.BFSShortestPath
import org.jgrapht.graph.DirectedPseudograph
import scala.collection.mutable
import scala.jdk.CollectionConverters.*

/** Graph algorithms used by the compiler (shortest paths with JGraphT). Results are deterministic:
 *  ties are broken by the order in which nodes are given. */
object Graphs:

  /** Strongly connected components of the graph `n → succ(n)`, in dependency order: if `a` depends on
   *  `b` (there is a path from `a` to `b`) and they are in different components, `b`'s component comes
   *  first. Nodes within a component keep the input order; successors outside `nodes` are ignored.
   *  Among the components whose dependencies are all listed, the one with the earliest node comes first
   *  (Kahn's algorithm with a priority queue on the condensation). */
  def components[N](nodes: Seq[N], succ: N => Seq[N]): List[List[N]] =
    val position = nodes.zipWithIndex.toMap
    val vertices = nodes.distinct.toVector
    val id = vertices.zipWithIndex.toMap
    // edges point from a dependency to its dependents, so a topological order lists dependencies first
    val out = Array.fill(vertices.length)(mutable.LinkedHashSet.empty[Int])
    for n <- nodes; m <- succ(n) if position.contains(m) do out(id(m)) += id(n)
    val comp = sccs(vertices.length, v => out(v))
    val count = if comp.isEmpty then 0 else comp.max + 1
    val members = Array.fill(count)(mutable.ArrayBuffer.empty[N])
    vertices.sortBy(position).foreach(v => members(comp(id(v))) += v)
    val first = members.map(ms => position(ms.head))
    val succs = Array.fill(count)(mutable.HashSet.empty[Int])
    for v <- vertices.indices; w <- out(v) if comp(v) != comp(w) do succs(comp(v)) += comp(w)
    val indegree = Array.fill(count)(0)
    for c <- 0 until count; d <- succs(c) do indegree(d) += 1
    val ready = mutable.PriorityQueue.empty[Int](Ordering.by[Int, Int](c => first(c)).reverse)
    for c <- 0 until count if indegree(c) == 0 do ready += c
    val order = mutable.ListBuffer.empty[List[N]]
    while ready.nonEmpty do
      val c = ready.dequeue()
      order += members(c).toList
      for d <- succs(c) do
        indegree(d) -= 1
        if indegree(d) == 0 then ready += d
    order.toList

  /** The strongly connected components of the graph on `0 until n` (Tarjan's algorithm, iterative): the
   *  component number of every vertex. */
  private def sccs(n: Int, out: Int => collection.Set[Int]): Array[Int] =
    val index = Array.fill(n)(-1)
    val low = Array.fill(n)(0)
    val onStack = Array.fill(n)(false)
    val comp = Array.fill(n)(-1)
    val stack = mutable.ArrayBuffer.empty[Int]
    var next = 0
    var count = 0
    for root <- 0 until n if index(root) < 0 do
      // the DFS path: a vertex with the iterator over its remaining successors
      val path = mutable.ArrayBuffer((root, out(root).iterator))
      index(root) = next; low(root) = next; next += 1
      stack += root; onStack(root) = true
      while path.nonEmpty do
        val (v, it) = path.last
        if it.hasNext then
          val w = it.next()
          if index(w) < 0 then
            index(w) = next; low(w) = next; next += 1
            stack += w; onStack(w) = true
            path += ((w, out(w).iterator))
          else if onStack(w) then low(v) = low(v).min(index(w))
        else
          path.remove(path.length - 1)
          if path.nonEmpty then
            val u = path.last._1
            low(u) = low(u).min(low(v))
          if low(v) == index(v) then
            var w = -1
            while w != v do
              w = stack.remove(stack.length - 1)
              onStack(w) = false
              comp(w) = count
            count += 1
    comp

  /** A shortest path (fewest edges) from `from` to `to` over the given edges; `Nil` if there is none or
   *  `from == to`. Parallel edges between the same nodes are allowed. */
  def shortestPath[N, E](edges: Seq[E], source: E => N, target: E => N, from: N, to: N): List[E] =
    if from == to then return Nil
    val g = new DirectedPseudograph[N, Wrapped[E]](classOf[Wrapped[E]])
    for (e, i) <- edges.zipWithIndex do
      val (s, t) = (source(e), target(e))
      g.addVertex(s)
      g.addVertex(t)
      g.addEdge(s, t, Wrapped(e, i))
    if !g.containsVertex(from) || !g.containsVertex(to) then return Nil
    Option(new BFSShortestPath(g).getPath(from, to)).map(_.getEdgeList.asScala.toList.map(_.edge)).getOrElse(Nil)

  /** Gives every edge its own identity, as JGraphT requires distinct edge objects. */
  private final case class Wrapped[E](edge: E, index: Int)
