package hugin.fuzz

import hugin.ir.*
import hugin.obj.{ArithOp, CmpOp, Prims}
import hugin.runtime.{Engine, ExtendedInt, Infinity}
import hugin.syntax.{AggKind, Bound, Literal}
import scala.collection.mutable

/** A naive reference evaluator of a core program (Definition 8.7): every component is evaluated by
 *  applying all of its rules to the full relations until nothing changes, with no deltas, no indexes and
 *  no identities. Words are structural: literals or [[NaiveEvaluator.Fact]]s (terms of any constructor),
 *  so interning is equality. A rule application adds `subfact_F` of its head: the head fact and its
 *  constructor subterms (every constructor is a fact constructor, REDESIGN §3.2).
 *  A relation with a bound column (docs/REDESIGN.md §5.2) keeps one fact per key, the best; after every
 *  round the values on positive-weight cycles of the value propagation graph become `∞` (Kaminski et
 *  al.'s Algorithm 1, literally: every round, cycles found by Floyd–Warshall).
 *  Written independently of [[hugin.runtime.Engine]] (it shares only the primitive operations, including
 *  the extended integers), to serve as the oracle of the differential fuzz test. */
final class NaiveEvaluator(prog: CoreProgram):
  import NaiveEvaluator.Fact

  /** The facts of each relation, by tag. */
  val facts: Vector[mutable.LinkedHashSet[Vector[Any]]] = prog.rels.map(_ => mutable.LinkedHashSet.empty[Vector[Any]])

  /** Seeds the relations with the facts already in an engine's store (the loaded input facts). */
  def load(engine: Engine): Unit =
    def word(w: Any): Any = w match
      case Id(rel, n) => Fact(rel, engine.store(rel).tuples(n).toVector.map(word))
      case other => other
    for (r, tag) <- engine.store.zipWithIndex; (t, n) <- r.tuples.zipWithIndex if r.current(n) do
      facts(tag) += t.toVector.map(word)

  // ------------------------------------------------------------------ words and expressions

  private def lit(w: Any): Option[Literal] = w match
    case l: java.lang.Long => Some(Literal.IntL(l))
    case d: java.lang.Double => Some(Literal.FloatL(d))
    case s: String => Some(Literal.StrL(s))
    case _ => None

  private def word(l: Literal): Any = l match
    case Literal.IntL(v) => java.lang.Long.valueOf(v)
    case Literal.FloatL(v) => java.lang.Double.valueOf(v)
    case Literal.StrL(v) => v

  /** Evaluates an expression. In a body a constructor term denotes its structure, whether or not it is a
   *  fact (comparisons are structural; existence is checked only by `Lookup`); in a head (`created`
   *  given), the constructor terms it builds are recorded in `created` (`subfact_F`). */
  private def eval(e: Expr, regs: Map[Int, Any], created: Option[mutable.ArrayBuffer[Fact]]): Option[Any] = e match
    case Expr.Reg(r) => regs.get(r)
    case Expr.Const(w) => Some(w)
    case Expr.Arith(op, l, r) =>
      for
        a <- eval(l, regs, created)
        b <- eval(r, regs, created)
        v <- (lit(a), lit(b)) match
          case (Some(x), Some(y)) => Prims.arith(op, x, y).map(word)
          case _ => ExtendedInt.arith(op, a, b)
      yield v
    case Expr.Neg(x) => eval(x, regs, created).flatMap(v => lit(v).fold(ExtendedInt.negate(v))(l => Prims.neg(l).map(word)))
    case Expr.Make(rel, as) =>
      val vs = as.toVector.map(eval(_, regs, created))
      if vs.exists(_.isEmpty) then None
      else
        val f = Fact(rel, vs.map(_.get))
        created.foreach(_ += f)
        Some(f)

  private def compare(op: CmpOp, a: Any, b: Any): Boolean = op match
    case CmpOp.Eq => a == b
    case CmpOp.Ne => a != b
    case _ => (lit(a), lit(b)) match
        case (Some(x), Some(y)) => Prims.cmp(op, x, y)
        case _ =>
          ExtendedInt.compare(a, b).exists { c =>
            op match
              case CmpOp.Lt => c < 0
              case CmpOp.Le => c <= 0
              case CmpOp.Gt => c > 0
              case _ => c >= 0
          }

  // ------------------------------------------------------------------ bodies

  /** All register files that satisfy `ops` (a conjunction), extending `regs`. */
  private def solve(ops: List[BodyOp], regs: Map[Int, Any]): LazyList[Map[Int, Any]] = ops match
    case Nil => LazyList(regs)
    case op :: rest =>
      // declaratively: the columns match if, with the bindings made, every check holds
      def matches(rel: Int, t: Vector[Any], binds: Array[(Int, Int)], checks: Array[(Int, Expr)]) =
        val rs = regs ++ binds.map((col, r) => r -> t(col))
        Option.when(checks.forall((col, e) => eval(e, rs, None).contains(t(col))))(rs)
      val next: LazyList[Map[Int, Any]] = op match
        case BodyOp.Scan(rel, _, asReg, binds, checks) =>
          LazyList.from(facts(rel).toList).flatMap { t =>
            matches(rel, t, binds, checks).map(rs => if asReg >= 0 then rs + (asReg -> Fact(rel, t)) else rs)
          }
        case BodyOp.Deref(src, rel, binds, checks) =>
          regs.get(src) match
            case Some(Fact(`rel`, t)) => LazyList.from(matches(rel, t, binds, checks))
            case _ => LazyList.empty
        case BodyOp.Tag(src, tags) =>
          regs.get(src) match
            case Some(Fact(rel, _)) if tags(rel) => LazyList(regs)
            case _ => LazyList.empty
        case BodyOp.Eval(dst, e) => LazyList.from(eval(e, regs, None).map(v => regs + (dst -> v)))
        case BodyOp.Test(op, a, b) =>
          (eval(a, regs, None), eval(b, regs, None)) match
            case (Some(x), Some(y)) if compare(op, x, y) => LazyList(regs)
            case _ => LazyList.empty
        case BodyOp.Lookup(dst, rel, as) =>
          // a fact-constructor term in a binding equation must be a fact
          val vs = as.toVector.map(eval(_, regs, None))
          if vs.forall(_.isDefined) && facts(rel).contains(vs.map(_.get)) then LazyList(regs + (dst -> Fact(rel, vs.map(_.get))))
          else LazyList.empty
        case BodyOp.NotIn(sub) => if solve(sub.toList, regs).isEmpty then LazyList(regs) else LazyList.empty
        case BodyOp.Agg(dst, kind, term, locals, sub) =>
          // one value of the term per distinct binding of the aggregate's variables (Definition 8.4)
          val groups = mutable.LinkedHashMap.empty[Vector[Option[Any]], Option[Any]]
          for rs <- solve(sub.toList, regs) do groups.getOrElseUpdate(locals.toVector.map(rs.get), eval(term, rs, None))
          LazyList.from(aggregate(kind, groups.values.toList).map(v => regs + (dst -> v)))
      next.flatMap(solve(rest, _))

  private def aggregate(kind: AggKind, vs: List[Option[Any]]): Option[Any] =
    if vs.exists(_.isEmpty) then None
    else
      val xs = vs.flatten
      kind match
        case AggKind.Count => Some(java.lang.Long.valueOf(xs.length.toLong))
        case AggKind.Sum =>
          xs.foldLeft(Option[Any](java.lang.Long.valueOf(0L))) { (acc, x) =>
            acc.flatMap(a =>
              (lit(a), lit(x)) match
                case (Some(p), Some(q)) => Prims.arith(ArithOp.Add, p, q).map(word)
                case _ => ExtendedInt.arith(ArithOp.Add, a, x)
            )
          }
        case AggKind.Min | AggKind.Max =>
          val ord: Ordering[Any] = (a, b) =>
            (lit(a), lit(b)) match
              case (Some(x), Some(y)) => Prims.compare(x, y).getOrElse(0)
              case _ => ExtendedInt.compare(a, b).getOrElse(0)
          if xs.isEmpty then None else Some(if kind == AggKind.Min then xs.min(ord) else xs.max(ord))

  // ------------------------------------------------------------------ fixpoint

  /** Evaluates the components in order, each to its fixpoint by naive iteration. */
  def run(): Unit =
    for comp <- prog.components do
      val rules = prog.rules.filter(r => comp.contains(r.headRel))
      var changed = true
      while changed do
        val derived = mutable.ArrayBuffer.empty[Fact]
        for r <- rules; regs <- solve(r.body.toList, Map.empty) do
          val created = mutable.ArrayBuffer.empty[Fact]
          val args = r.headArgs.toVector.map(eval(_, regs, Some(created)))
          if args.forall(_.isDefined) then derived ++= created += Fact(r.headRel, args.map(_.get))
        changed = false
        for f <- derived do if add(f) then changed = true
        if Limits.diverging(rules, this).exists(add) then changed = true

  /** The kind of a relation's bound column. */
  def bound(rel: Int): Option[Bound] = prog.rels(rel).boundColumn

  /** The value of a bound relation's key, if it has a fact. */
  def valueOf(rel: Int, key: Vector[Any]): Option[Any] = facts(rel).find(_.init == key).map(_.last)

  /** Adds a fact; for a bound relation, replaces the key's fact if the value is better. */
  private def add(f: Fact): Boolean = bound(f.rel) match
    case None => facts(f.rel).add(f.args)
    case Some(k) =>
      val old = valueOf(f.rel, f.args.init)
      val better = old.forall(o => ExtendedInt.compare(f.args.last, o).exists(c => if k == Bound.Min then c < 0 else c > 0))
      if better then
        old.foreach(o => facts(f.rel).remove(f.args.init :+ o))
        facts(f.rel).add(f.args)
      better

  /** The register files satisfying a rule's body, for [[Limits]]. */
  def solutions(r: CompiledRule): LazyList[Map[Int, Any]] = solve(r.body.toList, Map.empty)

  /** The head tuple of a rule for a register file, if defined. */
  def headOf(r: CompiledRule, regs: Map[Int, Any]): Option[Vector[Any]] =
    val args = r.headArgs.toVector.map(eval(_, regs, None))
    Option.when(args.forall(_.isDefined))(args.map(_.get))

  // ------------------------------------------------------------------ decoding

  /** Prints a word like [[hugin.runtime.Engine.show]]. */
  def show(w: Any, nested: Boolean = false): String = w match
    case Fact(rel, t) =>
      val s = (prog.rels(rel).displayName +: t.map(show(_, nested = true))).mkString(" ")
      if nested && t.nonEmpty then s"($s)" else s
    case s: String => Literal.quote(s)
    case l: java.lang.Long => if nested && l < 0 then s"($l)" else l.toString
    case d: java.lang.Double => val s = Literal.showDouble(d); if nested && d < 0 then s"($s)" else s
    case i: Infinity => if nested && i == Infinity.Neg then s"(${i.show})" else i.show
    case other => other.toString

  /** The facts of a relation, printed and sorted like [[hugin.runtime.Engine.facts]]. */
  def shown(rel: Int): List[String] = facts(rel).toList.map(t => show(Fact(rel, t)) + ".").sorted

object NaiveEvaluator:
  /** A fact as a structural word. */
  final case class Fact(rel: Int, args: Vector[Any])

/** The divergence step of Kaminski et al.'s Algorithm 1 for the naive evaluator: the value propagation
 *  graph of the current facts (an edge per rule, premise key and head key, weighted by the improvement,
 *  maximal over derivations) and the facts `∞` for the keys on positive-weight cycles, found with
 *  Floyd–Warshall over the max-plus semiring. Independent of `hugin.runtime.Divergence`, which uses
 *  Bellman–Ford, marks the nodes reachable from cycles too and checks at growing intervals. */
private object Limits:
  import NaiveEvaluator.Fact

  def diverging(rules: Seq[CompiledRule], ev: NaiveEvaluator): List[Fact] =
    val edges = mutable.HashMap.empty[(Fact, Fact), BigInt]
    for
      r <- rules if r.limitRegs.nonEmpty && ev.bound(r.headRel).isDefined
      regs <- ev.solutions(r)
      head <- ev.headOf(r, regs)
      v <- finite(head.last) if ev.valueOf(r.headRel, head.init).isDefined
      reg <- r.limitRegs
      case Fact(rel, t) <- regs.get(reg)
      l <- finite(t.last)
    do
      val w = (ev.bound(rel).contains(Bound.Max), ev.bound(r.headRel).contains(Bound.Max)) match
        case (true, true) => v - l
        case (false, false) => l - v
        case (true, false) => -v - l
        case (false, true) => v + l
      val e = (Fact(rel, t.init), Fact(r.headRel, head.init))
      if edges.get(e).forall(_ < w) then edges(e) = w
    val nodes = edges.keys.flatMap((a, b) => List(a, b)).toVector.distinct
    val n = nodes.length
    val at = nodes.zipWithIndex.toMap
    val d = Array.fill(n, n)(Option.empty[BigInt])
    for ((a, b), w) <- edges do d(at(a))(at(b)) = Some(w)
    for k <- 0 until n; i <- 0 until n; j <- 0 until n do
      for x <- d(i)(k); y <- d(k)(j) if d(i)(j).forall(_ < x + y) do d(i)(j) = Some(x + y)
    nodes.indices.toList.filter(i => d(i)(i).exists(_ > 0)).map { i =>
      val Fact(rel, key) = nodes(i)
      Fact(rel, key :+ (if ev.bound(rel).contains(Bound.Min) then Infinity.Neg else Infinity.Pos))
    }

  private def finite(w: Any): Option[BigInt] = w match
    case l: java.lang.Long => Some(BigInt(l.longValue))
    case _ => None
