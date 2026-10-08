package hugin.runtime

import hugin.ir.*
import hugin.obj.{ArithOp, CmpOp, Prims}
import hugin.syntax.{AggKind, Literal}
import scala.collection.mutable

/** Status of one component's evaluation. */
final case class ComponentStats(rels: Vector[String], rounds: Int)

/** Semi-naive evaluator over an interning store (Sections 9.1–9.7). */
final class Engine(prog: CoreProgram):
  val store: Vector[Relation] = prog.rels.zipWithIndex.map((r, i) => Relation(i, r, r.arity, prog.indexes.getOrElse(i, Set.empty)))
  val stats: mutable.ArrayBuffer[ComponentStats] = mutable.ArrayBuffer.empty

  // visibility windows per relation for the current round: old = [0, oldEnd), delta = [oldEnd, deltaEnd)
  private val oldEnd = Array.fill(store.length)(Int.MaxValue)
  private val deltaEnd = Array.fill(store.length)(Int.MaxValue)

  /** Which recursive atom of the rule being fired reads the delta (semi-naive evaluation): the atoms before
   *  it read the old part, the atoms after it the full relation; -1: all read the full relations. */
  private var deltaAt = -1

  // modes of `eval`
  private final val Dry = 0
  private final val InBody = 1
  private final val InHead = 2

  // ------------------------------------------------------------------ words and expressions

  private def arith(op: ArithOp, a: Any, b: Any): Option[Any] =
    (toLit(a), toLit(b)) match
      case (Some(x), Some(y)) => Prims.arith(op, x, y).map(fromLit)
      case _ => ExtendedInt.arith(op, a, b)

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
   *  is interned, and for aggregate terms, which are of base type or only counted); [[InBody]] looks up
   *  constructor terms ([[NonFact]] if absent); [[InHead]] interns every constructor term, which asserts
   *  it (`subfact_F`). */
  private def eval(e: Expr, regs: Array[Any], mode: Int): Option[Any] = e match
    case Expr.Reg(r) => Some(regs(r))
    case Expr.Const(w) => Some(w)
    case Expr.Arith(op, l, r) =>
      for a <- eval(l, regs, mode); b <- eval(r, regs, mode); v <- arith(op, a, b) yield v
    case Expr.Neg(x) =>
      eval(x, regs, mode).flatMap(v => toLit(v).fold(ExtendedInt.negate(v))(l => Prims.neg(l).map(fromLit)))
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
        else
          val n = r.lookup(vs)
          Some(if n >= 0 then Id(rel, n) else NonFact(rel, vs.toVector))

  /** [[eval]] without an `Option` per value, for the inner loops of joins: `null` if undefined (no word
   *  is `null`). Registers and constants, the most frequent expressions, allocate nothing. */
  private inline def word(e: Expr, regs: Array[Any], mode: Int): Any = e match
    case Expr.Reg(r) => regs(r)
    case Expr.Const(w) => w
    case _ => eval(e, regs, mode).getOrElse(null)

  private def compare(op: CmpOp, a: Any, b: Any): Boolean = op match
    case CmpOp.Eq => a == b
    case CmpOp.Ne => a != b
    case _ =>
      (toLit(a), toLit(b)) match
        case (Some(x), Some(y)) => Prims.cmp(op, x, y)
        case _ =>
          ExtendedInt.compare(a, b).exists(c =>
            op match
              case CmpOp.Lt => c < 0
              case CmpOp.Le => c <= 0
              case CmpOp.Gt => c > 0
              case _ => c >= 0
          )

  // ------------------------------------------------------------------ body execution

  /** The index of the columns a scan checks, per scan (looked up once, not per probe). */
  private val scanIndexes = java.util.IdentityHashMap[BodyOp.Scan, mutable.HashMap[Key, IntBuf]]()

  private def scanIndex(scan: BodyOp.Scan): mutable.HashMap[Key, IntBuf] =
    var idx = scanIndexes.get(scan)
    if idx == null then
      idx = store(scan.rel).index(scan.checks.map(_._1).toVector)
      scanIndexes.put(scan, idx)
    idx

  /** Runs ops(i..) and calls `k` for every solution. Returns false to stop early. */
  private def exec(ops: Array[BodyOp], i: Int, regs: Array[Any], k: Array[Any] => Boolean): Boolean =
    if i == ops.length then return k(regs)
    ops(i) match
      case scan @ BodyOp.Scan(rel, recIdx, asReg, binds, checks) =>
        val r = store(rel)
        // the window the atom reads (Section 9.5): old = [0, oldEnd), delta = [oldEnd, deltaEnd), full
        val lo = if recIdx >= 0 && recIdx == deltaAt then oldEnd(rel) else 0
        val hi =
          (if recIdx < 0 then Int.MaxValue
           else if deltaAt >= 0 && recIdx < deltaAt then oldEnd(rel)
           else deltaEnd(rel)) .min(r.size)
        // identities are in assertion order (see [[Relation]]). A tuple found through the index of the
        // checked columns has those values (the index compares with `equals`, which implies `==`), so
        // its checks are not evaluated again.
        def visit(n: Int, checked: Boolean): Boolean =
          val t = r.tuples(n)
          var ok = r.visible(n, hi)
          var j = if checked then checks.length else 0
          while ok && j < checks.length do
            val (col, e) = checks(j)
            val v = word(e, regs, InBody)
            if v == null || t(col) != v then ok = false
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
            val v = word(checks(j)._2, regs, InBody)
            if v == null then return true
            key(j) = v
            j += 1
          scanIndex(scan).get(Key(key)) match
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
                cont = visit(ids(from), checked = true)
                from += 1
              cont
        else
          var n = lo
          var cont = true
          while cont && n < hi do
            cont = visit(n, checked = false)
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
              val v = word(e, regs, InBody)
              if v == null || !(v == t(col)) then ok = false
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
              case _ => ExtendedInt.compare(a, b).getOrElse(0)
          Some(if kind == AggKind.Min then xs.min(ord) else xs.max(ord))

  // ------------------------------------------------------------------ rules and components

  private def fire(r: CompiledRule): Unit = derive(r, (vs, _) => store(r.headRel).intern(vs))

  /** Calls `k` with the head tuple and the register file of every derivation of `r` in the current
   *  windows. Arithmetic in the head is evaluated before any nested value is interned. */
  private def derive(r: CompiledRule, k: (Array[Any], Array[Any]) => Unit): Unit =
    val regs = new Array[Any](r.nregs.max(1))
    exec(
      r.body,
      0,
      regs,
      rs => {
        if r.headArgs.forall(e => word(e, rs, Dry) != null) then k(r.headArgs.map(e => word(e, rs, InHead)), rs)
        true
      }
    )

  /** Rounds after which a component with bound columns checks for divergence: 4, 8, 16, … A positive cycle
   *  of value propagation persists once it exists (stability), so checking at growing intervals keeps
   *  evaluation finite and costs a logarithmic number of passes. */
  private val FirstDivergenceCheck = 4

  /** Replaces the values that improve forever by `∞` ([[Divergence]]); the replacements join the delta. */
  private def checkDivergence(comp: Vector[Int], rules: Vector[CompiledRule]): Unit =
    deltaAt = -1
    if divergence.check(rules, derive) > 0 then comp.foreach(t => deltaEnd(t) = store(t).size)

  private lazy val divergence = Divergence(store)

  /** Whether the relation `rel` (-1: unknown) may have a non-empty delta. */
  private def hasDelta(rel: Int): Boolean = rel < 0 || deltaEnd(rel) > oldEnd(rel)

  /** The relation of each recursive atom of a rule, by its index (-1 if not found). */
  private val deltaRels = java.util.IdentityHashMap[CompiledRule, Array[Int]]()
  private def deltaRel(r: CompiledRule): Array[Int] =
    var rels = deltaRels.get(r)
    if rels == null then
      rels = Array.fill(r.recursiveAtoms)(-1)
      def visit(ops: Array[BodyOp]): Unit = ops.foreach {
        case BodyOp.Scan(rel, recIdx, _, _, _) if recIdx >= 0 => rels(recIdx) = rel
        case BodyOp.NotIn(sub) => visit(sub)
        case BodyOp.Agg(_, _, _, _, sub) => visit(sub)
        case _ =>
      }
      visit(r.body)
      deltaRels.put(r, rels)
    rels

  /** Evaluates all components. Cancellable: an interrupt of the evaluating thread ends evaluation with
   *  an `InterruptedException` at the next round (an editor that no longer needs the result). */
  def run(): Unit =
    val rulesByComp = prog.rules.groupBy(r => prog.components.indexWhere(_.contains(r.headRel)))
    for (comp, ci) <- prog.components.zipWithIndex do
      val rules = rulesByComp.getOrElse(ci, Vector.empty)
      // Init: every rule once, all atoms read the full relations
      comp.foreach { t =>
        oldEnd(t) = store(t).size; deltaEnd(t) = store(t).size
      }
      deltaAt = -1
      val before = comp.map(t => store(t).size)
      rules.foreach(fire)
      comp.foreach { t =>
        oldEnd(t) = before(comp.indexOf(t)); deltaEnd(t) = store(t).size
      }
      var rounds = 0
      var nextCheck = FirstDivergenceCheck
      val bounded = comp.exists(store(_).isBound)
      def deltaNonEmpty = comp.exists(t => deltaEnd(t) > oldEnd(t))
      val recursive = rules.filter(_.recursiveAtoms > 0)
      while deltaNonEmpty && recursive.nonEmpty do
        if Thread.interrupted() then throw InterruptedException("evaluation cancelled")
        rounds += 1
        // a variant whose delta atom has an empty delta derives nothing: skipped (Soufflé does the same)
        for r <- recursive; j <- 0 until r.recursiveAtoms if hasDelta(deltaRel(r)(j)) do
          deltaAt = j
          fire(r)
        comp.foreach { t =>
          oldEnd(t) = deltaEnd(t); deltaEnd(t) = store(t).size
        }
        if bounded && rounds >= nextCheck then
          checkDivergence(comp, rules)
          nextCheck *= 2
      comp.foreach { t =>
        oldEnd(t) = Int.MaxValue; deltaEnd(t) = Int.MaxValue
      }
      deltaAt = -1
      stats += ComponentStats(comp.map(prog.rels(_).name), rounds)

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
    case i: Infinity => if nested && i == Infinity.Neg then s"(${i.show})" else i.show
    case other => other.toString

  /** The facts of a relation, printed and sorted. For a relation with a bound column, the current (best) tuple of each key. */
  def facts(rel: Int): List[String] =
    val r = store(rel)
    r.tuples.indices.filter(r.current).map(n => show(Id(rel, n)) + ".").toList.sorted
