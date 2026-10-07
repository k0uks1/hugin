package hugin.fuzz

import hugin.ir.*
import hugin.obj.{ArithOp, CmpOp, Prims}
import hugin.runtime.Engine
import hugin.syntax.{AggKind, Literal}
import scala.collection.mutable

/** A naive reference evaluator of a core program (Definition 8.7): every component is evaluated by
 *  applying all of its rules to the full relations until nothing changes, with no deltas, no indexes and
 *  no identities. Words are structural: literals or [[NaiveEvaluator.Fact]]s (terms of any constructor),
 *  so interning is equality. A rule application adds `subfact_F` of its head: the head fact and its
 *  fact-constructor subterms, descending through data terms, which are values only and never facts.
 *  Written independently of [[hugin.runtime.Engine]] (it shares only the primitive operations), to
 *  serve as the oracle of the differential fuzz test. */
final class NaiveEvaluator(prog: CoreProgram):
  import NaiveEvaluator.Fact

  /** The facts of each relation, by tag (always empty for data constructors). */
  val facts: Vector[mutable.LinkedHashSet[Vector[Any]]] = prog.rels.map(_ => mutable.LinkedHashSet.empty[Vector[Any]])

  private val data: Vector[Boolean] = prog.rels.map(_.isData)

  /** Seeds the relations with the facts already in an engine's store (the loaded input facts). */
  def load(engine: Engine): Unit =
    def word(w: Any): Any = w match
      case Id(rel, n) => Fact(rel, engine.store(rel).tuples(n).toVector.map(word))
      case other => other
    for (r, tag) <- engine.store.zipWithIndex if !data(tag); t <- r.tuples do facts(tag) += t.toVector.map(word)

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
   *  given), the fact-constructor terms it builds are recorded in `created` (`subfact_F`). */
  private def eval(e: Expr, regs: Map[Int, Any], created: Option[mutable.ArrayBuffer[Fact]]): Option[Any] = e match
    case Expr.Reg(r) => regs.get(r)
    case Expr.Const(w) => Some(w)
    case Expr.Arith(op, l, r) =>
      for
        a <- eval(l, regs, created).flatMap(lit)
        b <- eval(r, regs, created).flatMap(lit)
        v <- Prims.arith(op, a, b)
      yield word(v)
    case Expr.Neg(x) => eval(x, regs, created).flatMap(lit).flatMap(Prims.neg).map(word)
    case Expr.Make(rel, as) =>
      val vs = as.toVector.map(eval(_, regs, created))
      if vs.exists(_.isEmpty) then None
      else
        val f = Fact(rel, vs.map(_.get))
        if !data(rel) then created.foreach(_ += f)
        Some(f)

  private def compare(op: CmpOp, a: Any, b: Any): Boolean = op match
    case CmpOp.Eq => a == b
    case CmpOp.Ne => a != b
    case _ => (lit(a), lit(b)) match
        case (Some(x), Some(y)) => Prims.cmp(op, x, y)
        case _ => false

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
            for a <- acc.flatMap(lit); b <- lit(x); v <- Prims.arith(ArithOp.Add, a, b) yield word(v)
          }
        case AggKind.Min | AggKind.Max =>
          val ord: Ordering[Any] = (a, b) =>
            (lit(a), lit(b)) match
              case (Some(x), Some(y)) => Prims.compare(x, y).getOrElse(0)
              case _ => 0
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
        for f <- derived do if facts(f.rel).add(f.args) then changed = true

  // ------------------------------------------------------------------ decoding

  /** Prints a word like [[hugin.runtime.Engine.show]]. */
  def show(w: Any, nested: Boolean = false): String = w match
    case Fact(rel, t) =>
      val s = (prog.rels(rel).displayName +: t.map(show(_, nested = true))).mkString(" ")
      if nested && t.nonEmpty then s"($s)" else s
    case s: String => Literal.quote(s)
    case l: java.lang.Long => if nested && l < 0 then s"($l)" else l.toString
    case d: java.lang.Double => val s = Literal.showDouble(d); if nested && d < 0 then s"($s)" else s
    case other => other.toString

  /** The facts of a relation, printed and sorted like [[hugin.runtime.Engine.facts]]. */
  def shown(rel: Int): List[String] = facts(rel).toList.map(t => show(Fact(rel, t)) + ".").sorted

object NaiveEvaluator:
  /** A fact as a structural word. */
  final case class Fact(rel: Int, args: Vector[Any])
