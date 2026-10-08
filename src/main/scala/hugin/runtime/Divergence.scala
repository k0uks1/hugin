package hugin.runtime

import hugin.ir.{CompiledRule, Id}
import hugin.syntax.Bound
import scala.collection.mutable

/** Divergence of bound columns (reference: object/bound-columns): the value propagation graph of Kaminski et al.
 *  (IJCAI 2017, "Tractability of Entailment: Stability") over the current values of a component, and the
 *  replacement of every value that would improve forever by `∞`.
 *
 *  A *node* is a key of a bound relation of the component. Every derivation of a rule whose head has a
 *  bound column contributes, for each atom of the component whose value flows into the head's bound
 *  column ([[CompiledRule.limitRegs]]), an edge from the atom's key (value `ℓ`) to the head's key (derived
 *  value `v`), weighted by how much the derivation improves on the premise: `v - ℓ` (`max → max`),
 *  `ℓ - v` (`min → min`), `-v - ℓ` (`max → min`), `v + ℓ` (`min → max`); an edge keeps its largest
 *  weight. For a type-consistent (hence stable) program every node on a cycle of positive weight has the
 *  value `∞` in the least fixpoint, and so has every node reachable from one: the edge's rule stays
 *  applicable and its head term is unbounded in the improving direction. Finite and infinite values are
 *  otherwise left to evaluation. */
final class Divergence(store: Vector[Relation]):
  private final case class Node(rel: Int, key: Key)

  /** The graph under construction: nodes are numbered, edges keep their maximal weight. */
  private final class Graph:
    val index = mutable.LinkedHashMap.empty[Node, Int]
    val edges = mutable.HashMap.empty[(Int, Int), BigInt]
    def node(n: Node): Int = index.getOrElseUpdate(n, index.size)
    def add(from: Node, to: Node, w: BigInt): Unit =
      val e = (node(from), node(to))
      if edges.get(e).forall(_ < w) then edges(e) = w

  /** Builds the value propagation graph from the derivations `derive` enumerates (the head tuple and the
   *  register file of each derivation of each rule), and replaces the values of the nodes on or reachable
   *  from positive cycles by `∞`. Returns the number of values replaced. */
  def check(rules: Iterable[CompiledRule], derive: (CompiledRule, (Array[Any], Array[Any]) => Unit) => Unit): Int =
    val g = Graph()
    for r <- rules if r.limitRegs.nonEmpty && store(r.headRel).isBound do
      derive(r, (head, regs) => edgesOf(r, head, regs, g))
    val diverging = reachableFromPositiveCycles(g)
    for (Node(rel, key), _) <- g.index if diverging(g.index(Node(rel, key))) do
      val r = store(rel)
      r.intern(key.ws :+ (if r.bound.contains(Bound.Min) then Infinity.Neg else Infinity.Pos))
    diverging.size

  private def edgesOf(r: CompiledRule, head: Array[Any], regs: Array[Any], g: Graph): Unit =
    val to = store(r.headRel)
    val headKey = Key(head.init)
    head.last match
      case v: java.lang.Long if to.hasKey(headKey) =>
        for reg <- r.limitRegs do
          regs(reg) match
            case Id(rel, n) =>
              val from = store(rel)
              from.tuples(n).last match
                case l: java.lang.Long =>
                  g.add(Node(rel, Key(from.tuples(n).init)), Node(r.headRel, headKey), weight(from, to, BigInt(l), BigInt(v)))
                case _ => // an infinite premise: its key is final already
            case _ =>
      case _ => // an infinite head value is stored as such by the derivation itself
  /** The improvement a derivation makes on its premise, in the directions of both columns. */
  private def weight(from: Relation, to: Relation, l: BigInt, v: BigInt): BigInt =
    (from.bound.contains(Bound.Max), to.bound.contains(Bound.Max)) match
      case (true, true) => v - l
      case (false, false) => l - v
      case (true, false) => -v - l
      case (false, true) => v + l

  /** The nodes on or reachable from a cycle of positive weight: Bellman–Ford for longest paths from all
   *  nodes at once; an edge that still relaxes after `|V|` rounds is reachable from a positive cycle, and
   *  every positive cycle has such an edge. */
  private def reachableFromPositiveCycles(g: Graph): Set[Int] =
    val n = g.index.size
    val dist = Array.fill(n)(BigInt(0))
    val edges = g.edges.toArray
    def relax(): Set[Int] =
      val changed = mutable.Set.empty[Int]
      for ((u, v), w) <- edges if dist(u) + w > dist(v) do
        dist(v) = dist(u) + w
        changed += v
      changed.toSet
    var round = 0
    var changed = relax()
    while changed.nonEmpty && round < n do
      round += 1
      changed = relax()
    if changed.isEmpty then Set.empty
    else
      val succ = edges.groupMap(_._1._1)(_._1._2)
      val seen = mutable.Set.from(changed)
      var frontier = changed.toList
      while frontier.nonEmpty do
        frontier = frontier.flatMap(u => succ.getOrElse(u, Array.empty[Int]).filter(seen.add))
      seen.toSet
