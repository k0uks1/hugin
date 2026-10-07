package hugin.runtime

import hugin.ir.*
import hugin.obj.{ArithOp, CmpOp, Prims}
import hugin.syntax.{AggKind, Literal}
import scala.collection.mutable

/** Status of one component's evaluation. */
final case class ComponentStats(rels: Vector[String], rounds: Int, truncated: Boolean)

/** Semi-naive evaluator over an interning store (Sections 9.1–9.7). */
final class Engine(prog: CoreProgram, budget: Option[Int]):
  val store: Vector[Relation] = prog.rels.zipWithIndex.map((r, i) => Relation(i, r, r.arity, prog.indexes.getOrElse(i, Set.empty)))
  val stats: mutable.ArrayBuffer[ComponentStats] = mutable.ArrayBuffer.empty
  var truncated = false

  // visibility windows per relation for the current round: old = [0, oldEnd), delta = [oldEnd, deltaEnd)
  private val oldEnd = Array.fill(store.length)(Int.MaxValue)
  private val deltaEnd = Array.fill(store.length)(Int.MaxValue)
  private var versionOf: Int => Version = _ => Version.Full

  // modes of `eval`
  private final val Dry = 0
  private final val InBody = 1
  private final val InHead = 2

  // ------------------------------------------------------------------ words and expressions

  private def arith(op: ArithOp, a: Any, b: Any): Option[Any] =
    (toLit(a), toLit(b)) match
      case (Some(x), Some(y)) => Prims.arith(op, x, y).map(fromLit)
      case _ => None

  def toLit(w: Any): Option[Literal] = w match
    case l: java.lang.Long => Some(Literal.IntL(l))
    case d: java.lang.Double => Some(Literal.FloatL(d))
    case s: String => Some(Literal.StrL(s))
    case _ => None

  def fromLit(l: Literal): Any = l match
    case Literal.IntL(v) => java.lang.Long.valueOf(v)
    case Literal.FloatL(v) => java.lang.Double.valueOf(v)
    case Literal.StrL(v) => v

  /** Evaluates an expression in one of three modes (see [[Expr.Make]]): [[Dry]] builds nothing (a
   *  constructor term is a placeholder; used to check that a head's arithmetic is defined before anything
   *  is interned, and for aggregate terms, which are of base type or only counted); [[InBody]] hash-conses
   *  data terms and looks up fact-constructor terms ([[NonFact]] if absent); [[InHead]] interns every
   *  constructor term, which asserts the fact-constructor ones (`subfact_F`). */
  private def eval(e: Expr, regs: Array[Any], mode: Int): Option[Any] = e match
    case Expr.Reg(r) => Some(regs(r))
    case Expr.Const(w) => Some(w)
    case Expr.Arith(op, l, r) =>
      for a <- eval(l, regs, mode); b <- eval(r, regs, mode); v <- arith(op, a, b) yield v
    case Expr.Neg(x) => eval(x, regs, mode).flatMap(toLit).flatMap(Prims.neg).map(fromLit)
    case Expr.Make(rel, as) =>
      val vs = new Array[Any](as.length)
      var nonFact = false
      var i = 0
      while i < as.length do
        eval(as(i), regs, mode) match
          case Some(v) =>
            vs(i) = v
            if v.isInstanceOf[NonFact] then nonFact = true
          case None => return None
        i += 1
      if mode == Dry then Some(Id(rel, -1))
      else
        val r = store(rel)
        if mode == InHead then Some(Id(rel, r.intern(vs)))
        else if nonFact then Some(NonFact(rel, vs.toVector))
        else if r.isData then Some(Id(rel, r.intern(vs)))
        else
          val n = r.lookup(vs)
          Some(if n >= 0 then Id(rel, n) else NonFact(rel, vs.toVector))

  private def compare(op: CmpOp, a: Any, b: Any): Boolean = op match
    case CmpOp.Eq => a == b
    case CmpOp.Ne => a != b
    case _ =>
      (toLit(a), toLit(b)) match
        case (Some(x), Some(y)) => Prims.cmp(op, x, y)
        case _ => false

  // ------------------------------------------------------------------ body execution

  private def range(rel: Int, recIdx: Int): (Int, Int) =
    if recIdx < 0 then (0, Int.MaxValue)
    else
      versionOf(recIdx) match
        case Version.Full => (0, deltaEnd(rel))
        case Version.Old => (0, oldEnd(rel))
        case Version.Delta => (oldEnd(rel), deltaEnd(rel))

  /** Runs ops(i..) and calls `k` for every solution. Returns false to stop early. */
  private def exec(ops: Array[BodyOp], i: Int, regs: Array[Any], k: Array[Any] => Boolean): Boolean =
    if i == ops.length then return k(regs)
    ops(i) match
      case BodyOp.Scan(rel, recIdx, asReg, binds, checks) =>
        val r = store(rel)
        val (lo, hi0) = range(rel, recIdx)
        val hi = hi0.min(r.size)
        // identities are in assertion order (see [[Relation]])
        def visit(n: Int): Boolean =
          val t = r.tuples(n)
          var ok = true
          var j = 0
          while ok && j < checks.length do
            val (col, e) = checks(j)
            eval(e, regs, InBody) match
              case Some(v) => if t(col) != v then ok = false
              case None => ok = false
            j += 1
          if ok then
            j = 0
            while j < binds.length do
              regs(binds(j)._2) = t(binds(j)._1)
              j += 1
            if asReg >= 0 then regs(asReg) = Id(rel, n)
            exec(ops, i + 1, regs, k)
          else true
        if checks.nonEmpty then
          val key = new Array[Any](checks.length)
          var j = 0
          while j < checks.length do
            eval(checks(j)._2, regs, InBody) match
              case Some(v) => key(j) = v
              case None => return true
            j += 1
          r.index(checks.map(_._1).toVector).get(Key(key)) match
            case None => true
            case Some(ids) =>
              // identities are ascending: restrict to the version window
              val snapshot = ids.length
              var from = 0
              if lo > 0 then
                var a = 0
                var b = snapshot
                while a < b do
                  val m = (a + b) >>> 1
                  if ids(m) < lo then a = m + 1 else b = m
                from = a
              var cont = true
              while cont && from < snapshot && ids(from) < hi do
                cont = visit(ids(from))
                from += 1
              cont
        else
          var n = lo
          var cont = true
          while cont && n < hi do
            cont = visit(n)
            n += 1
          cont
      case BodyOp.Deref(src, rel, binds, checks) =>
        regs(src) match
          case Id(`rel`, n) if n >= 0 =>
            val t = store(rel).tuples(n)
            var ok = true
            var j = 0
            while ok && j < checks.length do
              val (col, e) = checks(j)
              if !eval(e, regs, InBody).contains(t(col)) then ok = false
              j += 1
            if ok then
              binds.foreach((col, r) => regs(r) = t(col))
              exec(ops, i + 1, regs, k)
            else true
          case _ => true
      case BodyOp.Tag(src, tags) =>
        regs(src) match
          case Id(rel, _) if tags(rel) => exec(ops, i + 1, regs, k)
          case _ => true
      case BodyOp.Eval(dst, e) =>
        eval(e, regs, InBody) match
          case Some(v) if !v.isInstanceOf[NonFact] => regs(dst) = v; exec(ops, i + 1, regs, k)
          case _ => true
      case BodyOp.Test(op, a, b) =>
        (eval(a, regs, InBody), eval(b, regs, InBody)) match
          case (Some(x), Some(y)) if compare(op, x, y) => exec(ops, i + 1, regs, k)
          case _ => true
      case BodyOp.Lookup(dst, rel, as) =>
        val vs = as.map(eval(_, regs, InBody))
        if vs.exists(_.isEmpty) then true
        else
          val n = store(rel).lookup(vs.map(_.get))
          if n >= 0 then { regs(dst) = Id(rel, n); exec(ops, i + 1, regs, k) }
          else true
      case BodyOp.NotIn(sub) =>
        var found = false
        exec(sub, 0, regs, _ => { found = true; false })
        if found then true else exec(ops, i + 1, regs, k)
      case BodyOp.Agg(dst, kind, term, locals, sub) =>
        val seen = mutable.LinkedHashMap.empty[Key, Option[Any]]
        exec(
          sub,
          0,
          regs,
          rs => {
            seen.getOrElseUpdate(Key(locals.map(rs(_))), eval(term, rs, Dry))
            true
          }
        )
        aggregate(kind, seen.values.toList) match
          case Some(v) => regs(dst) = v; exec(ops, i + 1, regs, k)
          case None => true

  private def aggregate(kind: AggKind, vs: List[Option[Any]]): Option[Any] =
    if vs.exists(_.isEmpty) then return None
    val xs = vs.flatten
    kind match
      case AggKind.Count => Some(java.lang.Long.valueOf(xs.length.toLong))
      case AggKind.Sum =>
        xs.headOption match
          case None => Some(java.lang.Long.valueOf(0L))
          case Some(_) =>
            xs.tail.foldLeft(Option(xs.head))((acc, x) => acc.flatMap(a => arith(ArithOp.Add, a, x)))
      case AggKind.Min | AggKind.Max =>
        if xs.isEmpty then None
        else
          val ord: Ordering[Any] = (a: Any, b: Any) =>
            (toLit(a), toLit(b)) match
              case (Some(x), Some(y)) => Prims.compare(x, y).getOrElse(0)
              case _ => 0
          Some(if kind == AggKind.Min then xs.min(ord) else xs.max(ord))

  // ------------------------------------------------------------------ rules and components

  private def fire(r: CompiledRule): Unit =
    val regs = new Array[Any](r.nregs.max(1))
    exec(
      r.body,
      0,
      regs,
      rs => {
        // arithmetic in the head is evaluated before any nested value is interned
        if r.headArgs.forall(e => eval(e, rs, Dry).isDefined) then
          val vs = r.headArgs.map(eval(_, rs, InHead).get)
          store(r.headRel).intern(vs)
        true
      }
    )

  /** Evaluates all components. Cancellable: an interrupt of the evaluating thread ends evaluation with
   *  an `InterruptedException` at the next round (a non-terminating `%partial` component without budget). */
  def run(): Unit =
    val rulesByComp = prog.rules.groupBy(r => prog.components.indexWhere(_.contains(r.headRel)))
    for (comp, ci) <- prog.components.zipWithIndex do
      val rules = rulesByComp.getOrElse(ci, Vector.empty)
      val partial = comp.exists(t => prog.directives(t).partial)
      val limit = if partial then budget else None
      // Init: every rule once, all atoms read the full relations
      comp.foreach { t =>
        oldEnd(t) = store(t).size; deltaEnd(t) = store(t).size
      }
      versionOf = _ => Version.Full
      val before = comp.map(t => store(t).size)
      rules.foreach(fire)
      comp.foreach { t =>
        oldEnd(t) = before(comp.indexOf(t)); deltaEnd(t) = store(t).size
      }
      var rounds = 0
      var cut = false
      def deltaNonEmpty = comp.exists(t => deltaEnd(t) > oldEnd(t))
      val recursive = rules.filter(_.recursiveAtoms > 0)
      while deltaNonEmpty && recursive.nonEmpty && !cut do
        if Thread.interrupted() then throw InterruptedException("evaluation cancelled")
        if limit.exists(rounds >= _) then cut = true
        else
          rounds += 1
          for r <- recursive; j <- 0 until r.recursiveAtoms do
            versionOf = i => if i < j then Version.Old else if i == j then Version.Delta else Version.Full
            fire(r)
          comp.foreach { t =>
            oldEnd(t) = deltaEnd(t); deltaEnd(t) = store(t).size
          }
      if cut then truncated = true
      comp.foreach { t =>
        oldEnd(t) = Int.MaxValue; deltaEnd(t) = Int.MaxValue
      }
      versionOf = _ => Version.Full
      stats += ComponentStats(comp.map(prog.rels(_).name), rounds, cut)

  /** Answers of a query: distinct tuples of the user's variables. */
  def answers(q: CompiledQuery): List[Array[Any]] =
    val out = mutable.LinkedHashSet.empty[Key]
    for (alt, i) <- q.alternatives.zipWithIndex do
      val regs = new Array[Any](q.nregs.max(1))
      exec(alt, 0, regs, rs => { out += Key(q.regs(i).map(rs(_))); true })
    out.toList.map(_.ws)

  // ------------------------------------------------------------------ decoding

  /** Prints a word structurally, in the syntax of input facts (Section 9.6). */
  def show(w: Any, nested: Boolean = false): String = w match
    case Id(rel, n) =>
      val r = store(rel)
      val t = r.tuples(n)
      val s = (r.sym.displayName +: t.toVector.map(show(_, nested = true))).mkString(" ")
      if nested && t.nonEmpty then s"($s)" else s
    case s: String => Literal.quote(s)
    case l: java.lang.Long => if nested && l < 0 then s"($l)" else l.toString
    case d: java.lang.Double => val s = Literal.showDouble(d); if nested && d < 0 then s"($s)" else s
    case other => other.toString

  /** The facts of a relation, printed and sorted; none for a data constructor (its values are not facts). */
  def facts(rel: Int): List[String] =
    val r = store(rel)
    if r.isData then Nil else r.tuples.indices.map(n => show(Id(rel, n)) + ".").toList.sorted
