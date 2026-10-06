package hugin.util

import org.jgrapht.Graph
import org.jgrapht.alg.connectivity.KosarajuStrongConnectivityInspector
import org.jgrapht.alg.shortestpath.BFSShortestPath
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge, DirectedPseudograph}
import org.jgrapht.traverse.TopologicalOrderIterator
import scala.jdk.CollectionConverters.*

/** Graph algorithms used by the compiler, implemented with JGraphT. Results are deterministic:
 *  ties are broken by the order in which nodes are given. */
object Graphs:

  /** Strongly connected components of the graph `n → succ(n)`, in dependency order: if `a` depends on
   *  `b` (there is a path from `a` to `b`) and they are in different components, `b`'s component comes
   *  first. Nodes within a component keep the input order; successors outside `nodes` are ignored. */
  def components[N](nodes: Seq[N], succ: N => Seq[N]): List[List[N]] =
    val position = nodes.zipWithIndex.toMap
    val g = new DefaultDirectedGraph[N, DefaultEdge](classOf[DefaultEdge])
    nodes.foreach(g.addVertex)
    // edges point from a dependency to its dependents, so a topological order lists dependencies first
    for n <- nodes; m <- succ(n) if position.contains(m) do g.addEdge(m, n)
    val condensation: Graph[Graph[N, DefaultEdge], DefaultEdge] = new KosarajuStrongConnectivityInspector(g).getCondensation
    def first(c: Graph[N, DefaultEdge]): Int = c.vertexSet.asScala.map(position).min
    val byPosition: java.util.Comparator[Graph[N, DefaultEdge]] = (a, b) => Integer.compare(first(a), first(b))
    val order = new TopologicalOrderIterator(condensation, byPosition).asScala.toList
    order.map(c => c.vertexSet.asScala.toList.sortBy(position))

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
