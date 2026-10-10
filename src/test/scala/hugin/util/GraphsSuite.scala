package hugin.util

import org.scalacheck.{Gen, Prop}
import scala.util.hashing.MurmurHash3

/** [[Graphs.components]] (Tarjan's algorithm and Kahn's with a priority queue, issue #60) and
 *  [[Graphs.shortestPath]] (a breadth-first search, issue #58) replaced JGraphT. Both give exactly the
 *  results of the JGraphT implementations: the fingerprints below were recorded from them on the same
 *  generated graphs, before the dependency was removed. The properties check the results against
 *  definitions by reachability. */
class GraphsSuite extends munit.ScalaCheckSuite:
  /** The nodes reachable from `n` in one or more steps. */
  private def reachable(succ: Int => Seq[Int], n: Int): Set[Int] =
    Iterator.iterate((Set.empty[Int], succ(n).toSet)) { (seen, next) =>
      val all = seen ++ next
      (all, next.flatMap(succ).filterNot(all))
    }.dropWhile(_._2.nonEmpty).next()._1

  private val graphs: Gen[(List[Int], Map[Int, List[Int]])] =
    for
      n <- Gen.choose(0, 25)
      nodes <- Gen.pick(n, 0 until 40).map(_.toList)
      edges <- Gen.listOf(Gen.zip(Gen.choose(0, 45), Gen.choose(0, 45)))
    yield (nodes, edges.groupMap(_._1)(_._2))

  test("components and their order are those of the JGraphT implementation") {
    val rnd = scala.util.Random(60)
    val results = List.fill(5000) {
      val n = rnd.nextInt(25)
      val nodes = rnd.shuffle((0 until 40).toList).take(n)
      val succ = List.fill(rnd.nextInt(60))((rnd.nextInt(45), rnd.nextInt(45))).groupMap(_._1)(_._2)
      Graphs.components(nodes, k => succ.getOrElse(k, Nil)).map(_.mkString(",")).mkString(";")
    }
    assertEquals(MurmurHash3.orderedHash(results), 1591586826)
  }

  property("components are the mutually reachable nodes, dependencies first, in input order") {
    Prop.forAll(graphs) { (nodes, succ) =>
      val within = nodes.toSet
      val s = (n: Int) => succ.getOrElse(n, Nil).filter(within)
      val comps = Graphs.components(nodes, s)
      val reach = nodes.map(n => n -> reachable(s, n)).toMap
      val index = comps.zipWithIndex.flatMap((c, i) => c.map(_ -> i)).toMap
      comps.flatten.sorted == nodes.distinct.sorted &&
      comps.forall(c => c == nodes.distinct.filter(c.contains)) &&
      nodes.forall(a => nodes.forall(b => (index(a) == index(b)) == (a == b || reach(a)(b) && reach(b)(a)))) &&
      nodes.forall(a => reach(a).forall(b => index(b) <= index(a)))
    }
  }

  test("a long chain does not overflow the stack") {
    val n = 200000
    val comps = Graphs.components(0 until n, i => if i + 1 < n then List(i + 1) else Nil)
    assertEquals(comps.length, n)
    assertEquals(comps.head, List(n - 1))
  }

  private type Edge = (Int, Int, Int)
  private def path(edges: Seq[Edge], from: Int, to: Int): List[Edge] = Graphs.shortestPath[Int, Edge](edges, _._1, _._2, from, to)

  test("shortest paths are those of the JGraphT implementation (BFSShortestPath)") {
    val rnd = scala.util.Random(58)
    val results = List.newBuilder[String]
    for _ <- 0 until 20000 do
      val n = 1 + rnd.nextInt(12)
      val edges = Vector.tabulate(rnd.nextInt(40))(i => (rnd.nextInt(n + 2), rnd.nextInt(n + 2), i))
      for _ <- 0 until 4 do
        val (f, t) = (rnd.nextInt(n + 2), rnd.nextInt(n + 2))
        results += path(edges, f, t).map(_._3).mkString(",")
    assertEquals(MurmurHash3.orderedHash(results.result()), -1748971792)
  }

  private val edgeLists: Gen[(List[Edge], Int, Int)] =
    for
      raw <- Gen.listOf(Gen.zip(Gen.choose(0, 10), Gen.choose(0, 10)))
      from <- Gen.choose(0, 11)
      to <- Gen.choose(0, 11)
    yield (raw.zipWithIndex.map { case ((s, t), i) => (s, t, i) }, from, to)

  property("a shortest path is a path from `from` to `to` with the fewest edges") {
    Prop.forAll(edgeLists) { (edges, from, to) =>
      val succ = edges.groupMap(_._1)(_._2)
      val s = (n: Int) => succ.getOrElse(n, Nil)
      // the distance by breadth-first layers
      val distance = Iterator.iterate(Set(from))(layer => layer ++ layer.flatMap(s)).take(13).indexWhere(_(to))
      val p = path(edges, from, to)
      if from == to || distance < 0 then p.isEmpty
      else
        p.length == distance && p.head._1 == from && p.last._2 == to && p.zip(p.tail).forall((a, b) => a._2 == b._1)
    }
  }

  test("ties: the first parallel edge, and the path through the earlier edge") {
    assertEquals(path(List((0, 1, 0), (0, 1, 1)), 0, 1), List((0, 1, 0)))
    assertEquals(path(List((0, 2, 0), (0, 1, 1), (1, 3, 2), (2, 3, 3)), 0, 3), List((0, 2, 0), (2, 3, 3)))
    assertEquals(path(List((0, 1, 0), (1, 1, 1), (1, 0, 2)), 1, 1), Nil)
    assertEquals(path(List((0, 1, 0)), 1, 0), Nil)
    assertEquals(path(List((0, 1, 0)), 0, 7), Nil)
  }
