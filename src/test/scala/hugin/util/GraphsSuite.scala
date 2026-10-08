package hugin.util

import org.jgrapht.Graph
import org.jgrapht.alg.connectivity.KosarajuStrongConnectivityInspector
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import org.jgrapht.traverse.TopologicalOrderIterator
import org.scalacheck.{Gen, Prop}
import scala.jdk.CollectionConverters.*

/** [[Graphs.components]] (Tarjan's algorithm and Kahn's with a priority queue, issue #60) gives exactly
 *  the components and the order of the JGraphT implementation it replaced, kept here as the reference. */
class GraphsSuite extends munit.ScalaCheckSuite:
  private def reference[N](nodes: Seq[N], succ: N => Seq[N]): List[List[N]] =
    val position = nodes.zipWithIndex.toMap
    val g = new DefaultDirectedGraph[N, DefaultEdge](classOf[DefaultEdge])
    nodes.foreach(g.addVertex)
    for n <- nodes; m <- succ(n) if position.contains(m) do g.addEdge(m, n)
    val condensation: Graph[Graph[N, DefaultEdge], DefaultEdge] = new KosarajuStrongConnectivityInspector(g).getCondensation
    def first(c: Graph[N, DefaultEdge]): Int = c.vertexSet.asScala.map(position).min
    val byPosition: java.util.Comparator[Graph[N, DefaultEdge]] = (a, b) => Integer.compare(first(a), first(b))
    new TopologicalOrderIterator(condensation, byPosition).asScala.toList.map(c => c.vertexSet.asScala.toList.sortBy(position))

  private val graphs: Gen[(List[Int], Map[Int, List[Int]])] =
    for
      n <- Gen.choose(0, 25)
      nodes <- Gen.pick(n, 0 until 40).map(_.toList)
      edges <- Gen.listOf(Gen.zip(Gen.choose(0, 45), Gen.choose(0, 45)))
    yield (nodes, edges.groupMap(_._1)(_._2))

  property("components and their order are those of the JGraphT reference") {
    Prop.forAll(graphs) { (nodes, succ) =>
      val s = (n: Int) => succ.getOrElse(n, Nil)
      Graphs.components(nodes, s) == reference(nodes, s)
    }
  }

  test("a long chain does not overflow the stack") {
    val n = 200000
    val comps = Graphs.components(0 until n, i => if i + 1 < n then List(i + 1) else Nil)
    assertEquals(comps.length, n)
    assertEquals(comps.head, List(n - 1))
  }
