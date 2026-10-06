package hugin.obj

import hugin.util.*
import hugin.core.*
import hugin.meta.Tarjan
import scala.collection.mutable

/** An edge of the dependency graph (Section 6.4): `from` depends on `to`. */
final case class DepEdge(from: RelSym, to: RelSym, negative: Boolean, span: Span, rule: Rule)

object DepGraph:
  /** Relations occurring in a term (constructor patterns). */
  def relsIn(t: Term): List[RelSym] = t match
    case Term.App(r, as) => r.sym :: as.flatMap(relsIn)
    case Term.As(x, _) => relsIn(x)
    case Term.Ascr(x, _) => relsIn(x)
    case Term.Arith(_, l, r) => relsIn(l) ++ relsIn(r)
    case Term.Neg(x) => relsIn(x)
    case _ => Nil

  /** (relation, negative?, span) for every occurrence in a body. */
  def occurrences(body: List[Formula], neg: Boolean = false): List[(RelSym, Boolean, Span)] = body.flatMap {
    case a @ Formula.Atom(r, as, _) => (r.sym, neg, a.span) :: as.flatMap(relsIn).map(x => (x, neg, a.span))
    case n @ Formula.Not(a) => (a.rel.sym, true, n.span) :: a.args.flatMap(relsIn).map(x => (x, true, n.span))
    case g @ Formula.Agg(_, _, t, b) => relsIn(t).map(x => (x, true, g.span)) ++ occurrences(b, neg = true).map((r, _, s) => (r, true, s))
    case c @ Formula.Cmp(_, l, r) => (relsIn(l) ++ relsIn(r)).map(x => (x, neg, c.span))
    case Formula.Disj(alts) => occurrences(alts.flatten, neg)
    case _ => Nil
  }

  /** Constructor subpatterns of positive body atoms (the atoms themselves included). */
  def positiveSubpatterns(body: List[Formula]): Set[Term] =
    def subs(t: Term): List[Term] = t match
      case a @ Term.App(_, as) => a :: as.flatMap(subs)
      case Term.As(x, _) => subs(x)
      case Term.Ascr(x, _) => subs(x)
      case _ => Nil
    body.flatMap {
      case a @ Formula.Atom(r, as, _) => Term.App(r, as)(a.span) :: as.flatMap(subs)
      case _ => Nil
    }.toSet

  /** Constructor terms strictly inside the head's arguments that do not already exist in the body. */
  def newHeadConstructors(r: Rule): List[Term.App] =
    val existing = positiveSubpatterns(r.body)
    def inner(t: Term): List[Term.App] = t match
      case a @ Term.App(_, as) => (if existing(a) then Nil else List(a)) ++ as.flatMap(inner)
      case Term.As(x, _) => inner(x)
      case Term.Ascr(x, _) => inner(x)
      case Term.Arith(_, l, rr) => inner(l) ++ inner(rr)
      case Term.Neg(x) => inner(x)
      case _ => Nil
    r.heads.flatMap {
      case Term.App(_, as) => as.flatMap(inner)
      case _ => Nil
    }

  def edges(p: ObjProgram): List[DepEdge] =
    p.rules.toList.flatMap { r =>
      val heads = r.heads.collect { case Term.App(RelRef.Sym(c), _) => c }
      val occ = occurrences(r.body)
      val ctors = newHeadConstructors(r).map(_.rel.sym).distinct
      val fromHead = for h <- heads; (o, neg, sp) <- occ yield DepEdge(h, o, neg, sp, r)
      val fromCtors = for c <- ctors; (o, neg, sp) <- occ yield DepEdge(c, o, neg, sp, r)
      fromHead ++ fromCtors
    }

/** Phase: stratification (Section 6.4). Computes the evaluation order of components. */
final class StratifyPhase extends Phase:
  def phaseName = "stratify"
  def description = "dependency graph, components and stratification (Section 6.4)"

  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val es = DepGraph.edges(p)
    val succ = es.groupBy(_.from).view.mapValues(_.map(_.to).distinct).toMap
    val comps = Tarjan.components(p.rels.toList, (r: RelSym) => succ.getOrElse(r, Nil))
    ctx.unit.components = comps
    val compOf = comps.zipWithIndex.flatMap((c, i) => c.map(_ -> i)).toMap
    val reported = mutable.HashSet.empty[Int]
    for e <- es if e.negative && compOf(e.from) == compOf(e.to) && reported.add(compOf(e.from)) do
      // find a path back from `e.to` to `e.from` inside the component
      val inComp = es.filter(x => compOf(x.from) == compOf(e.from) && compOf(x.to) == compOf(e.from))
      val path = shortestPath(e.to, e.from, inComp)
      val cycle = (e :: path).map(x => (if x.negative then "not " else "") + x.to.name)
      var d = Diagnostic.error("E0601", "stratification cycle through negation", e.span,
        s"`${e.from.name}` depends negatively on `${e.to.name}`")
      d = d.withNote(s"cycle: ${e.from.name} -> ${cycle.mkString(" -> ")}")
      for x <- path.take(3) do d = d.withLabel(x.span, s"`${x.from.name}` depends on `${x.to.name}`")
      d = d.withNote("negation and aggregation must not occur in a recursive cycle (Section 6.4)")
      ctx.report(Diag.rule(e.rule)(d))

    // Facts constructed through nested heads in relations of *earlier* components can be missed by
    // readers evaluated in between (a gap in the ordering argument of Proposition 8.8); warn about it.
    val readers = p.rules.flatMap(r => DepGraph.occurrences(r.body).map(o => (o._1, r))).groupBy(_._1).view.mapValues(_.map(_._2)).toMap
    if ctx.settings.lint then
     for r <- p.rules; h <- r.heads.collectFirst { case Term.App(RelRef.Sym(c), _) if !c.isDerivation => c } do
      val hi = compOf(h)
      for t <- DepGraph.newHeadConstructors(r); c = t.rel.sym if compOf(c) < hi do
        val affected = readers.getOrElse(c, Vector.empty).filter(rr => (rr ne r) && rr.heads.exists {
          case Term.App(RelRef.Sym(x), _) => compOf(x) >= compOf(c) && compOf(x) <= hi
          case _ => false
        })
        affected.headOption.foreach { rr =>
          val reader = rr.heads.collectFirst { case Term.App(RelRef.Sym(x), _) => x.name }.getOrElse("?")
          ctx.report(Diag.rule(r)(Diagnostic.warning("W0004", s"facts of `${c.name}` constructed here may be missed by `$reader`", t.span,
            s"`${c.name}` is evaluated before `${h.name}`")
            .withLabel(rr.span, s"`$reader` reads `${c.name}`")
            .withNote("nested head constructors create facts of an earlier component after it was evaluated (see docs/NOTES.md)")))
        }

  private def shortestPath(from: RelSym, to: RelSym, es: List[DepEdge]): List[DepEdge] =
    if from == to then return Nil
    val prev = mutable.HashMap.empty[RelSym, DepEdge]
    val q = mutable.Queue(from)
    val seen = mutable.HashSet(from)
    while q.nonEmpty && !prev.contains(to) do
      val x = q.dequeue()
      for e <- es if e.from == x && seen.add(e.to) do
        prev(e.to) = e
        q.enqueue(e.to)
    var out = List.empty[DepEdge]
    var cur = to
    while prev.contains(cur) && cur != from do
      val e = prev(cur)
      out = e :: out
      cur = e.from
    out

  override def show(using Context): String =
    ctx.unit.components.zipWithIndex.map((c, i) => s"component $i: ${c.map(_.name).mkString(", ")}").mkString("\n")

/** Phase: completeness discipline (Section 6.5). */
final class CompletenessPhase extends Phase:
  def phaseName = "completeness"
  def description = "incomplete relations are never negated or aggregated over (Definition 6.6)"

  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val es = DepGraph.edges(p)
    // reason for incompleteness, propagated backwards along positive edges
    val why = mutable.LinkedHashMap.empty[RelSym, String]
    for r <- p.rels do
      if r.isOpen then why(r) = s"`${r.name}` is declared %open"
      else if r.isPartial then why(r) = s"`${r.name}` is declared %partial"
    var changed = true
    while changed do
      changed = false
      for e <- es if !e.negative && why.contains(e.to) && !why.contains(e.from) do
        why(e.from) = s"`${e.from.name}` depends positively on `${e.to.name}`; ${why(e.to)}"
        changed = true
    ctx.unit.incomplete = why.keySet.toSet
    for e <- es if e.negative && why.contains(e.to) do
      ctx.report(Diag.rule(e.rule)(Diagnostic.error("E0602", s"negation or aggregation over the incomplete relation `${e.to.name}`", e.span,
        "incomplete relation used negatively")
        .withNote(why(e.to))
        .withNote("the absence of a fact of an incomplete relation means unknown, not false (Definition 6.6)")))
    for q <- p.queries; (r, neg, sp) <- DepGraph.occurrences(q.body) if neg && why.contains(r) do
      ctx.report(Diag.query(q)(Diagnostic.error("E0602", s"query negates or aggregates over the incomplete relation `${r.name}`", sp, "used negatively")
        .withNote(why(r))
        .withNote("queries may mention incomplete relations only positively (Section 8.5)")))

  override def show(using Context): String =
    s"incomplete: ${ctx.unit.incomplete.map(_.name).toList.sorted.mkString(", ")}"

/** Phase: termination check (Section 10). */
final class TerminationPhase extends Phase:
  def phaseName = "termination"
  def description = "every growing component has a valid %terminates directive or is %partial (Section 10)"

  /** Why a rule is constructive (Definition 10.1), if it is. */
  def constructive(r: Rule): Option[(String, Span)] =
    DepGraph.newHeadConstructors(r).headOption.map(t => (s"its head constructs `${ObjPrinter.term(t)}`, which is not matched in the body", t.span))
      .orElse {
        val asVars = r.body.collect { case Formula.Atom(_, _, Some(v)) => v }.toSet
        val headVars = r.heads.flatMap(Moding.vars).toSet
        asVars.intersect(headVars).headOption.map(v => (s"the matched fact `${Var.display(v)}` is lifted into the head", r.span))
      }
      .orElse {
        def arith(t: Term): Option[Term] = t match
          case a: Term.Arith => Some(a)
          case n: Term.Neg => Some(n)
          case Term.App(_, as) => as.flatMap(arith).headOption
          case Term.As(x, _) => arith(x)
          case Term.Ascr(x, _) => arith(x)
          case _ => None
        r.heads.flatMap(arith).headOption.map(t => (s"its head computes `${ObjPrinter.term(t)}`", t.span))
      }
      .orElse {
        val headVars = r.heads.flatMap(Moding.vars).toSet
        r.body.collectFirst {
          case c @ Formula.Cmp(CmpOp.Eq, Term.Var(x), e) if headVars(x) && hasOp(e) => (s"head variable `$x` is computed by `${ObjPrinter.formula(c)}`", c.span)
          case c @ Formula.Cmp(CmpOp.Eq, e, Term.Var(x)) if headVars(x) && hasOp(e) => (s"head variable `$x` is computed by `${ObjPrinter.formula(c)}`", c.span)
        }
      }

  private def hasOp(t: Term): Boolean = t match
    case _: Term.Arith | _: Term.Neg => true
    case Term.App(_, as) => as.exists(hasOp)
    case _ => false

  private def headRel(r: Rule): Option[RelSym] = r.heads.headOption.collect { case Term.App(RelRef.Sym(c), _) => c }

  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val es = DepGraph.edges(p)
    val compOf = ctx.unit.components.zipWithIndex.flatMap((c, i) => c.map(_ -> i)).toMap
    val rulesByComp = p.rules.groupBy(r => headRel(r).flatMap(compOf.get).getOrElse(-1))
    for (comp, ci) <- ctx.unit.components.zipWithIndex do
      val inC = comp.toSet
      val recursive = comp.length > 1 || es.exists(e => e.from == comp.head && e.to == comp.head)
      val rules = rulesByComp.getOrElse(ci, Vector.empty)
      val constructiveRules = rules.flatMap(r => constructive(r).map(r -> _))
      if recursive && constructiveRules.nonEmpty && !comp.exists(_.isPartial) then
        val candidates = comp.filter(_.terminates.isDefined)
        if candidates.isEmpty then
          val (r, (why, sp)) = constructiveRules.head
          val names = comp.filterNot(c => c.isCtor || c.isDemand).map(_.name)
          ctx.report(Diag.rule(r)(Diagnostic.error("E0603", "growing component without a valid %terminates directive", sp, why)
            .withNote(s"the recursive component {${comp.map(_.name).mkString(", ")}} contains this constructive rule, so its fixed point may be infinite")
            .withHelp(names.headOption.map(n => s"declare a structurally decreasing argument, e.g. `%terminates X ($n ...)`, or mark the relation `%partial $n.`").getOrElse("mark a relation of the component %partial"))))
        else
          val results = candidates.map(c => c -> validate(c, inC, rules))
          if !results.exists(_._2.isEmpty) then
            val (c, Some((msg, sp, rule))) = results.head: @unchecked
            var d = Diagnostic.error("E0604", s"invalid `%terminates` directive for `${c.name}`", sp, msg)
            d = d.withLabel(c.terminates.get._2, "directive declared here")
            ctx.report(rule.map(r => Diag.rule(r)(d)).getOrElse(d))

  /** Checks Definition 10.3; returns the first violation. */
  private def validate(c: RelSym, inC: Set[RelSym], rules: Vector[Rule]): Option[(String, Span, Option[Rule])] =
    val k = c.terminates.get._1
    def isDemandOf(r: RelSym) = r.kind match
      case RelKind.Demand(of, _) => of == c
      case _ => false
    // every rule of C whose head is neither c nor a demand relation of c is non-constructive
    rules.find(r => headRel(r).exists(h => h != c && !isDemandOf(h)) && constructive(r).isDefined).map { r =>
      (s"another constructive relation in the component: `${headRel(r).get.name}` (${constructive(r).get._1})", constructive(r).get._2, Some(r))
    }.orElse {
      val numeric = c.cols.lift(k).exists(col => col.tpe == OType.Int || (col.tpe match { case OType.Con(s, _) => s.kind.isInstanceOf[TypeKind.Refinement]; case _ => false }))
      if !c.hasModes then
        rules.filter(r => headRel(r).contains(c)).iterator.map { r =>
          val Term.App(_, hs) = r.heads.head: @unchecked
          val atomsOfC = r.body.collect { case a @ Formula.Atom(RelRef.Sym(x), _, _) if inC(x) => a }
          atomsOfC.find(_.rel.sym != c).map(a => (s"the rule calls `${a.rel.sym.name}`, which is in the same component", a.span, Some(r)))
            .orElse(atomsOfC.iterator.map { call =>
              val s = call.args(k)
              val h = hs(k)
              if !decreases(s, h, r.body) then
                Some((s"no decrease: `${ObjPrinter.term(s)}` is not smaller than `${ObjPrinter.term(h)}`", call.span, Some(r)))
              else if !anchored(s, h, r.body, inC, numeric) then
                val msg =
                  if numeric then s"no anchor: the body does not bound `${ObjPrinter.term(s)}` by a literal (e.g. `${ObjPrinter.term(s)} < 100`)"
                  else s"no anchor: the variables of `${ObjPrinter.term(h)}` are not bound by a relation outside the component"
                Some((msg, call.span, Some(r)))
              else None
            }.collectFirst { case Some(v) => v })
        }.collectFirst { case Some(v) => v }
      else
        val notInput = c.modes.find((m, _) => !m.inputs.lift(k).contains(true))
        notInput.map((m, sp) => (s"argument ${k + 1} is not an input of mode ${m.show}", sp, None)).orElse {
          rules.filter(r => headRel(r).exists(isDemandOf) && r.body.exists {
            case Formula.Atom(RelRef.Sym(x), _, _) => inC(x)
            case _ => false
          }).iterator.map { r =>
            val Term.App(RelRef.Sym(d), us) = r.heads.head: @unchecked
            val pos = inputIndex(d, c, k)
            r.body.headOption match
              case Some(g @ Formula.Atom(RelRef.Sym(gd), ws, _)) if isDemandOf(gd) =>
                val gpos = inputIndex(gd, c, k)
                (pos, gpos) match
                  case (Some(i), Some(j)) =>
                    val u = us(i)
                    val w = ws(j)
                    if !decreases(u, w, r.body) then Some((s"no decrease: demand `${ObjPrinter.term(u)}` is not smaller than `${ObjPrinter.term(w)}`", r.heads.head.span, Some(r)))
                    else if numeric && !r.body.exists {
                        case Formula.Cmp(CmpOp.Gt | CmpOp.Ge, x, Term.Lit(_)) => x == u
                        case Formula.Cmp(CmpOp.Lt | CmpOp.Le, Term.Lit(_), x) => x == u
                        case _ => false
                      } then Some((s"no anchor: demand `${ObjPrinter.term(u)}` is not bounded below", r.heads.head.span, Some(r)))
                    else None
                  case _ => Some(("the terminating argument is not an input of the demand", r.span, Some(r)))
              case _ => Some(("a demand rule without guard", r.span, Some(r)))
          }.collectFirst { case Some(v) => v }
        }
    }

  private def inputIndex(d: RelSym, c: RelSym, k: Int): Option[Int] = d.kind match
    case RelKind.Demand(_, m) if m.inputs.lift(k).contains(true) => Some(m.inputs.take(k).count(identity))
    case _ => None

  /** u ≺ w: structural (u a variable strictly inside the pattern w) or numeric (w = u + l). */
  private def decreases(u: Term, w: Term, body: List[Formula]): Boolean =
    def strictlyInside(v: String, t: Term): Boolean = t match
      case Term.App(_, as) => as.exists(a => Moding.vars(a).contains(v))
      case Term.As(x, _) => strictlyInside(v, x)
      case Term.Ascr(x, _) => strictlyInside(v, x)
      case _ => false
    def plus(big: Term, small: Term): Boolean = big match
      case Term.Arith(ArithOp.Add, x, Term.Lit(hugin.syntax.Literal.IntL(l))) => x == small && l > 0
      case Term.Arith(ArithOp.Add, Term.Lit(hugin.syntax.Literal.IntL(l)), x) => x == small && l > 0
      case _ => false
    def minus(small: Term, big: Term): Boolean = small match
      case Term.Arith(ArithOp.Sub, x, Term.Lit(hugin.syntax.Literal.IntL(l))) => x == big && l > 0
      case _ => false
    val structural = u match
      case Term.Var(v) => strictlyInside(v, w)
      case _ => false
    structural || plus(w, u) || minus(u, w) || body.exists {
      case Formula.Cmp(CmpOp.Eq, a, b) => (a == w && plus(b, u)) || (b == w && plus(a, u)) || (a == u && minus(b, w)) || (b == u && minus(a, w))
      case _ => false
    }

  private def anchored(s: Term, h: Term, body: List[Formula], inC: Set[RelSym], numeric: Boolean): Boolean =
    val hv = Moding.vars(h)
    val boundOutside = body.collect { case Formula.Atom(RelRef.Sym(x), as, v) if !inC(x) => as.flatMap(Moding.vars).toSet ++ v }.flatten.toSet
    val structuralAnchor = hv.nonEmpty && hv.subsetOf(boundOutside)
    val numericAnchor = numeric && body.exists {
      case Formula.Cmp(CmpOp.Lt | CmpOp.Le, x, Term.Lit(_)) => x == s
      case Formula.Cmp(CmpOp.Gt | CmpOp.Ge, Term.Lit(_), x) => x == s
      case _ => false
    }
    structuralAnchor || numericAnchor
