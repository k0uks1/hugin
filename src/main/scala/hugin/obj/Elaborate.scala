package hugin.obj

import hugin.util.*
import hugin.compiler.*
import scala.collection.mutable

/** Section 7.1: projections `X.l` and updates `(X with {...})` on a closed type with members c1..cn
 *  are expanded into one copy of the rule per member; copy i adds `(ci Z̄ as X)`. */
final class Records extends MiniPhase:
  def phaseName = "records"
  def description = "expand projections and updates (Section 7.1)"

  private var ops: TypeOps | Null = null
  override def prepare(using Context): Unit = ops = TypeOps(ctx.unit.prog.nn)

  private def projected(t: Term, acc: mutable.LinkedHashSet[String]): Unit = t match
    case Term.Proj(Term.Var(x), _) => acc += x
    case Term.With(Term.Var(x), fs) => acc += x; fs.foreach(f => projected(f._2, acc))
    case Term.App(_, as) => as.foreach(projected(_, acc))
    case Term.As(y, _) => projected(y, acc)
    case Term.Ascr(y, _) => projected(y, acc)
    case Term.Arith(_, l, r) => projected(l, acc); projected(r, acc)
    case Term.Neg(y) => projected(y, acc)
    case _ =>

  private def projectedF(f: Formula, acc: mutable.LinkedHashSet[String]): Unit = f match
    case Formula.Atom(_, as, _) => as.foreach(projected(_, acc))
    case Formula.Cmp(_, l, r) => projected(l, acc); projected(r, acc)
    case Formula.Not(a) => projectedF(a, acc)
    case Formula.Agg(_, _, t, b) => projected(t, acc); b.foreach(projectedF(_, acc))
    case Formula.Disj(alts) => alts.flatten.foreach(projectedF(_, acc))
    case _ =>

  private def zName(x: String, c: RelSym, k: Int): String =
    s"$x.${c.cols(k).label.getOrElse((k + 1).toString)}"

  /** Rewrites projections/updates of the variables in `choice` (var → chosen member). */
  private def rw(t: Term, choice: Map[String, RelSym]): Term = t match
    case p @ Term.Proj(Term.Var(x), l) if choice.contains(x) =>
      val c = choice(x)
      Term.Var(zName(x, c, c.labelIndex(l).get))(p.span)
    case w @ Term.With(Term.Var(x), fs) if choice.contains(x) =>
      val c = choice(x)
      val args = c.cols.indices.map { k =>
        fs.find(f => c.cols(k).label.contains(f._1)) match
          case Some((_, h, _)) => rw(h, choice)
          case None => Term.Var(zName(x, c, k))(w.span)
      }.toList
      Term.App(RelRef.Sym(c), args)(w.span)
    case a @ Term.App(r, as) => Term.App(r, as.map(rw(_, choice)))(a.span)
    case a @ Term.As(y, v) => Term.As(rw(y, choice), v)(a.span)
    case a @ Term.Ascr(y, tp) => Term.Ascr(rw(y, choice), tp)(a.span)
    case a @ Term.Arith(op, l, r) => Term.Arith(op, rw(l, choice), rw(r, choice))(a.span)
    case n @ Term.Neg(y) => Term.Neg(rw(y, choice))(n.span)
    case other => other

  private def guardFor(x: String, c: RelSym, span: Span): Formula =
    Formula.Atom(RelRef.Sym(c), c.cols.indices.map(k => Term.Var(zName(x, c, k))(span): Term).toList, Some(x))(span)

  /** Rewrites a body; guards are added to the innermost body that mentions the projection. */
  private def rwBody(b: List[Formula], choice: Map[String, RelSym], span: Span): List[Formula] =
    val here = mutable.LinkedHashSet.empty[String]
    b.foreach {
      case Formula.Agg(_, _, _, _) | Formula.Disj(_) =>
      case f => projectedF(f, here)
    }
    val rewritten = b.map {
      case a @ Formula.Atom(r, as, v) => Formula.Atom(r, as.map(rw(_, choice)), v)(a.span)
      case c @ Formula.Cmp(op, l, r) => Formula.Cmp(op, rw(l, choice), rw(r, choice))(c.span)
      case n @ Formula.Not(a) => Formula.Not(Formula.Atom(a.rel, a.args.map(rw(_, choice)), a.as)(a.span))(n.span)
      case g @ Formula.Agg(res, k, t, ib) =>
        val inner = rwBody(ib, choice, g.span)
        val termVars = mutable.LinkedHashSet.empty[String]
        projected(t, termVars)
        val extra = termVars.toList.filter(x =>
          choice.contains(x) && !inner.exists {
            case Formula.Atom(_, _, Some(`x`)) => true
            case _ => false
          }
        ).map(x => guardFor(x, choice(x), g.span))
        Formula.Agg(res, k, rw(t, choice), inner ++ extra)(g.span)
      case d @ Formula.Disj(alts) => Formula.Disj(alts.map(rwBody(_, choice, d.span)))(d.span)
      case other => other
    }
    rewritten ++ here.toList.filter(choice.contains).map(x => guardFor(x, choice(x), span))

  private def expand(
      heads: List[Term],
      body: List[Formula],
      gamma: Map[String, OType],
      span: Span
  ): List[(List[Term], List[Formula], Map[String, OType])] =
    val vs = mutable.LinkedHashSet.empty[String]
    heads.foreach(projected(_, vs))
    body.foreach(projectedF(_, vs))
    if vs.isEmpty then return List((heads, body, gamma))
    val choices = vs.toList.foldLeft(List(Map.empty[String, RelSym])) { (acc, x) =>
      val ms = gamma.get(x).map(t => ops.nn.members(t).toList.sortBy(_.id)).getOrElse(Nil)
      for m <- acc; c <- ms yield m + (x -> c)
    }
    choices.map { ch =>
      val headVarsProj = mutable.LinkedHashSet.empty[String]
      heads.foreach(projected(_, headVarsProj))
      val hs = heads.map(rw(_, ch))
      var b = rwBody(body, ch, span)
      // projections occurring only in heads need their guard in the top-level body
      for
        x <- headVarsProj if ch.contains(x) && !b.exists {
          case Formula.Atom(_, _, Some(`x`)) => true
          case _ => false
        }
      do b = b :+ guardFor(x, ch(x), span)
      val g2 =
        gamma ++ ch.flatMap((x, c) => c.cols.indices.map(k => zName(x, c, k) -> c.cols(k).tpe)) ++ ch.map((x, c) => x -> OType.Fact(c, Nil))
      (hs, b, g2)
    }

  override def transformRule(r: Rule)(using Context): List[Rule] =
    val g = Option(ctx.unit.varTypes.get(r)).getOrElse(Map.empty)
    expand(r.heads, r.body, g, r.span).map { (hs, b, g2) =>
      val nr = r.withParts(heads = hs, body = b)
      ctx.unit.varTypes.put(nr, g2)
      nr
    }

  override def transformQuery(q: Query)(using Context): Query =
    val g = Option(ctx.unit.varTypes.get(q)).getOrElse(Map.empty)
    expand(Nil, q.body, g, q.span) match
      case List((_, b, g2)) => val nq = q.withBody(b); ctx.unit.varTypes.put(nq, g2); nq
      case many =>
        // alternatives of a query are kept as one top-level disjunction, expanded when lowering
        val nq = q.withBody(List(Formula.Disj(many.map(_._2))(q.span)))
        ctx.unit.varTypes.put(nq, many.map(_._3).reduce(_ ++ _))
        nq

/** Section 7.2: split disjunctions (and multi-head rules) into several rules. */
final class Disjunctions extends MiniPhase:
  def phaseName = "disjunction"
  def description = "split disjunctions and multiple heads (Section 7.2)"

  private def split(body: List[Formula]): List[List[Formula]] =
    val idx = body.indexWhere(_.isInstanceOf[Formula.Disj])
    if idx < 0 then List(body)
    else
      val Formula.Disj(alts) = body(idx): @unchecked
      alts.flatMap(alt => split(body.take(idx) ++ alt ++ body.drop(idx + 1)))

  private def checkNested(body: List[Formula], report: Diagnostic => Unit): Boolean =
    body.forall {
      case g @ Formula.Agg(_, _, _, b) =>
        val inner = b.exists(_.isInstanceOf[Formula.Disj])
        if inner then
          report(Diagnostic.error(
            "E0202",
            "disjunction inside an aggregate is not supported",
            g.span,
            "this aggregate's body contains a disjunction"
          )
            .withHelp("define a helper relation with one rule per alternative and aggregate over it"))
        !inner && checkNested(b, report)
      case _ => true
    }

  override def transformRule(r: Rule)(using Context): List[Rule] =
    if !checkNested(r.body, d => ctx.report(Diag.rule(r)(d))) then return Nil
    val g = ctx.unit.varTypes.get(r)
    for h <- r.heads; b <- split(r.body) yield
      val nr = r.withParts(heads = List(h), body = b)
      if g != null then ctx.unit.varTypes.put(nr, g)
      nr

  override def transformQuery(q: Query)(using Context): Query =
    if !checkNested(q.body, d => ctx.report(Diag.query(q)(d))) then q.withBody(Nil)
    else
      split(q.body) match
        case List(b) => q.withBody(b)
        case alts =>
          val nq = q.withBody(List(Formula.Disj(alts)(q.span)))
          val g = ctx.unit.varTypes.get(q)
          if g != null then ctx.unit.varTypes.put(nq, g)
          nq

/** Section 7.3: demand transformation (magic sets) for relations with declared modes. */
final class DemandPhase extends Phase:
  def phaseName = "demand"
  def description = "demand transformation for moded relations (Section 7.3)"

  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val demandRels = mutable.LinkedHashMap.empty[(RelSym, Mode), RelSym]
    def demand(c: RelSym, m: Mode): RelSym =
      demandRels.getOrElseUpdate(
        (c, m), {
          val d = RelSym(s"${c.name}^d[${m.show}]", RelKind.Demand(c, m), c.span, c.origin)
          d.cols = c.cols.zip(m.inputs).filter(_._2).map(_._1)
          d
        }
      )
    def inputs(args: List[Term], m: Mode): List[Term] = args.zip(m.inputs).filter(_._2).map(_._1)

    // 1. guarding
    val guarded = p.rules.flatMap { r =>
      r.heads match
        case List(h @ Term.App(RelRef.Sym(c), args)) if c.hasModes =>
          c.modes.map { (m, _) =>
            val g = Formula.Atom(RelRef.Sym(demand(c, m)), inputs(args, m), None)(h.span)
            val nr = r.withParts(body = g :: r.body)
            val gt = ctx.unit.varTypes.get(r)
            if gt != null then ctx.unit.varTypes.put(nr, gt)
            nr
          }
        case _ => List(r)
    }
    // 2. propagation
    val seen = mutable.HashSet.empty[String]
    val propagation = mutable.ArrayBuffer.empty[Rule]
    def propagate(body: List[Formula], span: Span, origin: Origin, expansions: List[Expansion], name: Option[String]): Unit =
      Moding.canonical(body, Set.empty) match
        case Left(_) => // reported by `moding`
        case Right((ordered, _)) =>
          def walk(prefix: List[Formula], fs: List[Formula], b: Set[String]): Unit = fs match
            case Nil =>
            case f :: rest =>
              def call(a: Formula.Atom): Unit =
                val c = a.rel.sym
                if c.hasModes then
                  Moding.firstApplicable(c, a.args, b).foreach { m =>
                    val head = Term.App(RelRef.Sym(demand(c, m)), inputs(a.args, m))(a.span)
                    val r = Rule(name.map(n => s"$n^d"), List(head), prefix)(span, origin, expansions)
                    if seen.add(ObjPrinter.rule(r)) then propagation += r
                  }
              f match
                case a: Formula.Atom => call(a)
                case Formula.Not(a) => call(a)
                case Formula.Agg(_, _, _, ib) =>
                  Moding.canonical(ib, b) match
                    case Right((iordered, _)) => walk(prefix, iordered, b)
                    case Left(_) =>
                case _ =>
              val b2 = Moding.step(f, b).getOrElse(b)
              walk(prefix :+ f, rest, b2)
          walk(Nil, ordered, Set.empty)
    for r <- guarded do propagate(r.body, r.span, r.origin, r.expansions, r.name)
    for q <- p.queries do
      q.body match
        case List(Formula.Disj(alts)) => alts.foreach(a => propagate(a, q.span, q.origin, q.expansions, None))
        case b => propagate(b, q.span, q.origin, q.expansions, None)
    p.rules = guarded ++ propagation
    p.rels = p.rels ++ demandRels.values

  override def show(using Context): String = ObjPrinter.program(ctx.unit.prog.nn)

/** Section 7.4: derivation relations for rules under `%derivations`. */
final class DerivationsPhase extends Phase:
  def phaseName = "derivations"
  def description = "introduce derivation relations (Section 7.4)"

  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val names = ctx.unit.derivationRules
    def baseName(n: String): String = n.indexOf('[') match
      case -1 => n
      case i => n.substring(0, i)
    def wanted(r: Rule): Boolean = r.name.exists { n =>
      !n.endsWith("^d") && (names.contains(baseName(n)) || r.heads.exists {
        case Term.App(RelRef.Sym(c), _) => c.derivations || c.instanceOf.exists(_._1.derivations)
        case _ => false
      })
    }
    val groups = p.rules.filter(wanted).groupBy(_.name.get)
    if groups.isEmpty then return
    val replaced = mutable.HashMap.empty[Rule, List[Rule]]
    val newRels = mutable.ArrayBuffer.empty[RelSym]
    for (name, rs) <- groups.toList.sortBy(_._1); (r, i) <- rs.zipWithIndex do
      val rn = if rs.length == 1 then s"@$name" else s"@$name#${i + 1}"
      val head = r.heads.head
      val Term.App(RelRef.Sym(c), _) = head: @unchecked
      var k = 0
      val atoms = mutable.ListBuffer.empty[(RelSym, String)]
      val body = r.body.map {
        case a @ Formula.Atom(RelRef.Sym(rel), args, as) =>
          k += 1
          val v = as.getOrElse(s"I#$k")
          atoms += ((rel, v))
          Formula.Atom(RelRef.Sym(rel), args, Some(v))(a.span)
        case other => other
      }
      val d = RelSym(rn, RelKind.Derivation(name), r.span, r.origin)
      d.cols = (Column(None, OType.Fact(c, Nil)) :: atoms.toList.map((rel, _) => Column(None, OType.Fact(rel, Nil)))).toVector
      d.isOutput = true
      newRels += d
      val r1 = r.withParts(body = body)
      val dh = Term.App(RelRef.Sym(d), head :: atoms.toList.map((_, v) => Term.Var(v)(r.span)))(r.span)
      val r2 = Rule(Some(rn), List(dh), body)(r.span, r.origin, r.expansions)
      replaced(r) = List(r1, r2)
    p.rules = p.rules.flatMap(r => replaced.getOrElse(r, List(r)))
    p.rels = p.rels ++ newRels

  override def show(using Context): String = ObjPrinter.program(ctx.unit.prog.nn)
