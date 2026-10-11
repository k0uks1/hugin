package hugin.runtime

import hugin.ir.{CompiledRule, CoreProgram, Expr, Id}
import scala.collection.mutable

/** Evaluation that reuses an earlier one (issue #126, PR 4): the longest prefix of the steps of the new
 *  evaluation (loading the facts files, then the components in the program's order) whose keys
 *  ([[ComponentKeys]]) equal those of the earlier evaluation's first steps is not run again: the
 *  relations as they were after those steps are copied from the earlier engine, and evaluation continues
 *  with the next component. In the REPL, a new rule changes its component and those after it in the
 *  order; the components before are copied, not evaluated.
 *
 *  The result is the evaluation from scratch, tuple for tuple: equal keys mean the same rules over the
 *  same facts in the same order, so the state after the prefix is the one a new evaluation reaches, with
 *  the same identities, and the rest is evaluated as from scratch. (Continuing a component that only
 *  gained rules from its old relations would number its facts in another order; it is not done.) */
object Reuse:
  /** What an evaluation records for a later one: the facts files, and the sizes of the relations that
   *  changed in each step (after loading the facts; after each component, in the program's order). */
  final class Trace(val facts: List[Evaluation.ParsedFacts], val sizes: Vector[Map[Int, Int]])

  /** The earlier evaluation: its program, object program, engine and trace. */
  final case class Earlier(prog: CoreProgram, obj: hugin.obj.ObjProgram, engine: Engine, trace: Trace)

  /** The number of components copied by the last evaluations (for tests), and those evaluated. */
  val copied: java.util.concurrent.atomic.AtomicLong = java.util.concurrent.atomic.AtomicLong()

  /** Copies into `engine` the state of `earlier` after its first steps that equal this evaluation's (at
   *  least the facts), with the sizes of those steps in `engine`'s tags. `None` if nothing is reused
   *  (the facts or the relations they read differ), and the engine is still empty. */
  def restore(
      engine: => Engine,
      prog: CoreProgram,
      keys: ComponentKeys,
      facts: List[Evaluation.ParsedFacts],
      earlier: Earlier
  ): Option[(Int, Vector[Map[Int, Int]])] =
    def texts(fs: List[Evaluation.ParsedFacts]) = fs.map(_.text)
    def names(fs: List[Evaluation.ParsedFacts]) = fs.flatMap(_.names).toSet
    if texts(facts) != texts(earlier.trace.facts) then return None
    val old = ComponentKeys(earlier.prog, earlier.obj)
    if old.facts(texts(earlier.trace.facts), names(earlier.trace.facts)) != keys.facts(texts(facts), names(facts)) then return None
    var named = keys.named
    var steps = 0
    val comps = prog.components.length.min(earlier.prog.components.length).min(earlier.trace.sizes.length - 1)
    while steps < comps && old.component(steps) == keys.component(steps) do
      steps += 1
      named = keys.named
    // the tags of the relations named in the equal steps, in both programs
    val oldToNew = mutable.HashMap.empty[Int, Int]
    for i <- 0 until named do oldToNew(old.tagOf(i)) = keys.tagOf(i)
    val sizes = earlier.trace.sizes.take(steps + 1)
    val at = sizes.foldLeft(Map.empty[Int, Int])(_ ++ _)
    if !at.forall((t, n) => n == 0 || oldToNew.contains(t)) || !copy(engine, earlier.engine, at, oldToNew) then return None
    for ci <- 0 until steps; st <- earlier.engine.statsOf(ci) do engine.setStats(ci, st)
    copied.addAndGet(steps)
    Some((steps, sizes.map(_.map((t, n) => oldToNew(t) -> n))))

  /** Interns the first `sizes(t)` tuples of each relation `t` of `from` into `into`, in order (the same
   *  identities; a bound relation's improvements replayed), relation and nested identities moved to
   *  `into`'s tags. False if a value names a relation without a tag in `into`. */
  private def copy(into: Engine, from: Engine, sizes: Map[Int, Int], tags: collection.Map[Int, Int]): Boolean =
    def move(w: Any): Any = w match
      case Id(r, n) => Id(tags.getOrElse(r, throw Unmapped()), n)
      case other => other
    try
      for (t, n) <- sizes.toVector.sortBy(_._1) if n > 0 do
        val src = from.store(t).tuples
        val dst = into.store(tags(t))
        for i <- 0 until n do dst.intern(src(i).map(move))
      true
    catch case _: Unmapped => false

  private final class Unmapped extends Exception(null, null, false, false)

  /** The relations a component's evaluation can add tuples to: its members and the constructors its rules
   *  assert in their heads. */
  def writes(prog: CoreProgram, ci: Int, rules: Vector[CompiledRule]): Set[Int] =
    def made(e: Expr): List[Int] = e match
      case Expr.Make(r, args) => r :: args.toList.flatMap(made)
      case Expr.Arith(_, l, r) => made(l) ++ made(r)
      case Expr.Neg(x) => made(x)
      case _ => Nil
    prog.components(ci).toSet ++ rules.flatMap(_.headArgs.flatMap(made))
