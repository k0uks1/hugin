package hugin.obj
package check

import hugin.util.*
import hugin.compiler.*

import hugin.obj.typing.Moding

/** Phase: termination check (Section 10).
 *
 *  A recursive component with a constructive rule (Definition 10.1) needs a `%partial` relation or a
 *  measure that every recursive step decreases (Definition 10.3, generalised as described in
 *  `docs/NOTES.md`, "Termination"):
 *
 *  - a measure is a tuple of argument positions per relation, compared lexicographically; slots hold
 *    integers (ordered by `<`) or terms (ordered by the proper-subterm relation);
 *  - every relation of the component that is called recursively by a measured relation has a measure of
 *    the same shape, so mutual recursion is accepted when the measures decrease along every call;
 *  - decreases and bounds are derived by interval reasoning over the linear (in)equalities of the body
 *    (see [[Arithmetic]]), not only syntactically.
 *
 *  Unmoded (bottom-up) components: the call is smaller than the head and the call's measure lies in a
 *  finite set (anchor). Moded (demand-driven) components: each demand is smaller than the demand that
 *  guards it, and integer slots are bounded below where they decrease. */
final class TerminationPhase extends Phase:
  def phaseName = "termination"
  def description = "every growing component has a valid %terminates directive or is %partial (Section 10)"

  /** Why a rule of the component `inC` is constructive (Definition 10.1, refined), if it is.
   *
   *  A rule is constructive if it builds a constructor term, data or fact, that is not matched in the body,
   *  in a head (also through a head variable bound by a binding equation `X = c t̄` with a data term, which
   *  builds the value) or in a moded input (the head of a demand rule). Such a term counts only if it can
   *  take infinitely many values: a ground term (`red`, `mk 1`) is one fixed term, and a term whose
   *  variables are all [[Termination.finiteVars]] ranges over finitely many valuations, since the relations
   *  binding them are complete and finite when the component is evaluated (induction over the evaluation
   *  order). See docs/NOTES.md, "Termination" (issue #1, F3).
   */
  def constructive(r: Rule, inC: RelSym => Boolean): Option[(String, Span)] =
    val finite = Termination.finiteVars(r.body, inC)
    val headVars = r.heads.flatMap(Moding.vars).toSet
    val atomVars = r.body.collect { case Formula.Atom(_, as, v) => as.flatMap(Moding.vars).toSet ++ v }.flatten.toSet
    val existing = DepGraph.positiveSubpatterns(r.body)
    def builds(t: Term): Boolean = t match
      case a @ Term.App(RelRef.Sym(c), as) => (c.isData && !existing(a)) || as.exists(builds)
      case Term.As(x, _) => builds(x)
      case Term.Ascr(x, _) => builds(x)
      case _ => false
    DepGraph.newHeadConstructors(r, withHead = true).find(t => !Moding.vars(t).subsetOf(finite)).map(t =>
      (s"its head constructs `${ObjPrinter.term(t)}`, which is not matched in the body", t.span)
    )
      .orElse {
        // `X = c t̄` with a data term binds `X` to a new value unless `X` is bound by an atom (a test)
        r.body.collectFirst(Function.unlift {
          case c @ Formula.Cmp(CmpOp.Eq, l, rr) =>
            List((l, rr), (rr, l)).collectFirst {
              case (Term.Var(x), e) if headVars(x) && !atomVars(x) && builds(e) && !Moding.vars(e).subsetOf(finite) =>
                (s"head variable `${Var.display(x)}` is built by `${ObjPrinter.formula(c)}`", c.span)
            }
          case _ => None
        })
      }
      .orElse {
        val asVars = r.body.collect { case Formula.Atom(_, _, Some(v)) => v }.toSet
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
        r.body.collectFirst {
          case c @ Formula.Cmp(CmpOp.Eq, Term.Var(x), e) if headVars(x) && hasOp(e) =>
            (s"head variable `${Var.display(x)}` is computed by `${ObjPrinter.formula(c)}`", c.span)
          case c @ Formula.Cmp(CmpOp.Eq, e, Term.Var(x)) if headVars(x) && hasOp(e) =>
            (s"head variable `${Var.display(x)}` is computed by `${ObjPrinter.formula(c)}`", c.span)
        }
      }

  private def hasOp(t: Term): Boolean = t match
    case _: Term.Arith | _: Term.Neg => true
    case Term.App(_, as) => as.exists(hasOp)
    case _ => false

  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val es = DepGraph.edges(p)
    val compOf = ctx.unit.components.zipWithIndex.flatMap((c, i) => c.map(_ -> i)).toMap
    val rulesByComp = p.rules.groupBy(r => Termination.headRel(r).flatMap(compOf.get).getOrElse(-1))
    for (comp, ci) <- ctx.unit.components.zipWithIndex do
      val inC = comp.toSet
      val recursive = comp.length > 1 || es.exists(e => e.from == comp.head && e.to == comp.head)
      val rules = rulesByComp.getOrElse(ci, Vector.empty)
      val constructiveRules = rules.flatMap(r => constructive(r, inC).map(r -> _))
      val names = Termination.showComponent(comp)
      def explain(s: String): Unit = if ctx.settings.explainTermination then ctx.unit.explanations += s
      // a cycle through negation or aggregation is a stratification error (E0601), reported already;
      // it arises e.g. for the demand of an auxiliary relation of an aggregate (issue #1, B4)
      val stratified = !es.exists(e => e.negative && inC(e.from) && inC(e.to))
      if recursive && stratified then
        if constructiveRules.isEmpty then
          explain(s"termination: $names: finite: recursive, but no rule is constructive (no numbers, no new terms beyond a finite set)")
        else if comp.exists(ctx.unit.facts(_).partial) then
          val partial = comp.filter(ctx.unit.facts(_).partial).map(r => s"`${r.name}`").mkString(", ")
          explain(s"termination: $names: not checked: $partial is %partial (evaluated with the round budget)")
        else
          // a component of demand relations only is measured by the relations they are demands of
          val measures = comp.map(Termination.base).flatMap(c => ctx.unit.facts(c).terminates.map(t => c -> t._1)).toMap
          val analysis = Termination(this, ctx.unit.facts, comp, rules, p.rules, es)
          if measures.isEmpty then
            val (r, (why, sp)) = constructiveRules.head
            explain(s"termination: $names: rejected: no %terminates directive (E0603)")
            ctx.report(Diag.rule(r)(noMeasure(analysis, r, why, sp)))
          else
            analysis.check(measures) match
              case Right(lines) => explain((s"termination: $names: terminates" :: lines).mkString("\n"))
              case Left(f) =>
                explain(s"termination: $names: rejected: ${f.message} (E0604)")
                ctx.report(f.diagnostic)

  /** E0603: a growing component without a measure, with a measure suggestion when one can be found. */
  private def noMeasure(a: Termination, r: Rule, why: String, sp: Span)(using Context): Diagnostic =
    val comp = a.comp
    var d = Diagnostic.error("E0603", "growing component without a valid %terminates directive", sp, why)
      .withNote(
        s"the recursive component ${Termination.showComponent(comp)} contains this constructive rule, so its fixed point may be infinite"
      )
    Termination.headRel(r).flatMap(a.cycle).foreach(c => d = d.withNote(s"recursion: ${c.map(x => s"`${x.name}`").mkString(" -> ")}"))
    if ctx.unit.splitRules.contains(r) then
      Termination.headRel(r).foreach(c =>
        d = d.withNote(
          s"the rule asserts the fact `${ObjPrinter.term(r.heads.head)}` of `${c.name}`, so it is also evaluated in `${c.name}`'s component (Proposition 8.8, see docs/NOTES.md)"
        )
      )
    a.suggest match
      case Some(directives) =>
        d.withHelp(s"this measure is accepted: ${directives.mkString(" ")}")
      case None =>
        val names = comp.map(Termination.base).filter(c => c.kind == RelKind.Plain || DepGraph.isFactCtor(c)).distinct.map(_.name)
        d.withHelp(names.headOption.map(n =>
          s"declare a decreasing argument, e.g. `%terminates X ($n ...)`, or mark the relation `%partial $n.` to evaluate it with a round budget"
        ).getOrElse("mark a relation of the component %partial"))

/** A violation of the termination conditions, with everything the diagnostic shows. */
final case class TerminationFailure(
    message: String,
    span: Span,
    label: String,
    rule: Option[Rule],
    directive: Option[Span],
    secondary: List[(Span, String)] = Nil,
    notes: List[String] = Nil,
    helps: List[String] = Nil
):
  def diagnostic: Diagnostic =
    var d = Diagnostic.error("E0604", message, span, label)
    for (s, l) <- secondary if s.exists do d = d.withLabel(s, l)
    for s <- directive if s.exists do d = d.withLabel(s, "measure declared here")
    notes.foreach(n => d = d.withNote(n))
    helps.foreach(h => d = d.withHelp(h))
    rule.map(r => Diag.rule(r)(d)).getOrElse(d)

/** The termination analysis of one recursive component `comp` with rules `rules` (Section 10). */
final class Termination(
    phase: TerminationPhase,
    facts: ProgramFacts,
    val comp: List[RelSym],
    rules: Vector[Rule],
    allRules: Vector[Rule],
    es: List[DepEdge]
):
  import Termination.*

  private val inC = comp.toSet

  /** The shortest cycle through `c` inside the component (for diagnostics). */
  def cycle(c: RelSym): Option[List[RelSym]] =
    val succ = es.filter(e => inC(e.from) && inC(e.to)).groupMap(_.from)(_.to)
    val prev = scala.collection.mutable.LinkedHashMap.empty[RelSym, RelSym]
    var frontier = List(c)
    var found = false
    while frontier.nonEmpty && !found do
      frontier = frontier.flatMap { x =>
        succ.getOrElse(x, Nil).distinct.filter { y =>
          if y == c then
            if !found then prev(c) = x
            found = true
            false
          else if prev.contains(y) then false
          else
            prev(y) = x
            true
        }
      }
    if !found then None
    else
      var path = List(c)
      var x = prev(c)
      while x != c do
        path = x :: path
        x = prev(x)
      Some(c :: path)

  /** A measure that would be accepted: one integer or structural argument per relation, or a
   *  lexicographic pair for a single relation. Rendered as directives. */
  def suggest: Option[List[String]] =
    val rels = comp.map(base).distinct.filter(c => c.kind == RelKind.Plain && c.arity > 0)
    def positions(c: RelSym) = (0 until c.arity).toList
    val singles: Iterator[Map[RelSym, List[Int]]] =
      if rels.isEmpty || rels.length > 3 then Iterator.empty
      else
        rels.foldLeft(Iterator(Map.empty[RelSym, List[Int]]))((acc, c) =>
          acc.flatMap(m => positions(c).iterator.map(k => m.updated(c, List(k))))
        ).take(64)
    val pairs: Iterator[Map[RelSym, List[Int]]] = rels match
      case List(c) => for i <- positions(c).iterator; j <- positions(c).iterator if i != j yield Map(c -> List(i, j))
      case _ => Iterator.empty
    (singles ++ pairs).find(m => check(m).isRight).map(m => rels.map(c => directive(c, m(c))))

  /** Checks the component with the given measures; the explanation, or the first violation.
   *
   *  A moded component is checked per strongly connected component of its *demand* graph (an edge `c → e`
   *  for every demand rule `e^d … :- c^d …`): demands only flow along that graph, so a call from one group
   *  into another (`typed` calling `lookup`, which never calls back) needs no decrease; the pair (rank of
   *  the group in the acyclic demand graph, measure) decreases lexicographically along every demand. The
   *  dependency graph may still join such groups into one component through answers (`typed` reads
   *  `lookup`, whose demands come from `typed`'s). Measures are compared, and need the same shape, only
   *  within a group. */
  def check(measures: Map[RelSym, List[Int]]): Either[TerminationFailure, List[String]] =
    val groups =
      if !measures.keys.exists(facts.hasModes) then List(measures.keys.toList)
      else
        val measured = measures.keys.toList.sortBy(_.name)
        def demandBase(x: RelSym) = x.kind match
          case RelKind.Demand(of, _) if measures.contains(of) => Some(of)
          case _ => None
        val edges = allRules.flatMap { r =>
          for
            e <- headRel(r).flatMap(demandBase)
            c <- r.body.collectFirst { case Formula.Atom(RelRef.Sym(x), _, _) if x.isDemand => x }.flatMap(demandBase)
          yield c -> e
        }
        hugin.util.Graphs.components(measured, c => edges.collect { case (`c`, e) => e }.distinct)
    groups.foldLeft[Either[TerminationFailure, List[String]]](Right(Nil)) { (acc, g) =>
      acc.flatMap(lines => checkGroup(measures.filter((c, _) => g.contains(c)), measures).map(lines ++ _))
    }

  /** Checks one group of relations whose measures are compared with each other (see [[check]]); `all` are
   *  the measures of the whole component. */
  private def checkGroup(measures: Map[RelSym, List[Int]], all: Map[RelSym, List[Int]]): Either[TerminationFailure, List[String]] =
    val measured = measures.keys.toList.sortBy(_.name)
    def declared(c: RelSym) = facts(c).terminates.map(_._2)
    val first = measured.head
    val n = measures(first).length
    def slotNumeric(c: RelSym, k: Int) = c.cols.lift(k).exists(col => isInt(col.tpe))
    val shapeError = measured.collectFirst {
      case c if measures(c).length != n =>
        TerminationFailure(
          s"measures of different lengths in the component ${showComponent(comp)}",
          declared(c).getOrElse(c.span),
          s"`${c.name}` is measured by ${plural(measures(c).length)}",
          None,
          None,
          declared(first).toList.map(_ -> s"`${first.name}` is measured by ${plural(n)}"),
          notes = List("measures of mutually recursive relations are compared with each other, so they need the same shape")
        )
      case c if (0 until n).exists(i => slotNumeric(c, measures(c)(i)) != slotNumeric(first, measures(first)(i))) =>
        val i = (0 until n).find(i => slotNumeric(c, measures(c)(i)) != slotNumeric(first, measures(first)(i))).get
        TerminationFailure(
          s"measures of different types in the component ${showComponent(comp)}",
          declared(c).getOrElse(c.span),
          s"component ${i + 1} of `${c.name}`'s measure is ${kind(slotNumeric(c, measures(c)(i)))}",
          None,
          None,
          declared(first).toList.map(
            _ -> s"component ${i + 1} of `${first.name}`'s measure is ${kind(slotNumeric(first, measures(first)(i)))}"
          )
        )
    }
    val slots = (0 until n).toList.map(i => slotNumeric(first, measures(first)(i)))
    val ctx = Ctx(measures, slots, all)
    shapeError.toLeft(()).flatMap { _ =>
      if measured.exists(facts.hasModes) then moded(ctx) else bottomUp(ctx)
    }.map { lines =>
      val ms = measured.map(c =>
        s"  measure of `${c.name}`: ${showPositions(c, measures(c))}${if n > 1 then " (lexicographic)" else ""}"
      )
      ms ++ lines
    }

  private final case class Ctx(measures: Map[RelSym, List[Int]], slots: List[Boolean], all: Map[RelSym, List[Int]]):
    def of(c: RelSym): List[Int] = measures(c)
    def has(c: RelSym): Boolean = measures.contains(c)

    /** Measured in the component, possibly in another group (see [[Termination.check]]). */
    def measuredAnywhere(c: RelSym): Boolean = all.contains(c)
    def directive(c: RelSym): Option[Span] = facts(c).terminates.map(_._2)

  /** Rules of relations without a measure (other than demand relations of measured ones) must not be
   *  constructive: their facts consist of existing terms. With `answers`, in a demand-driven component, the
   *  answers of measured relations count as finite sources (there are finitely many demands, see
   *  [[moded]]), so `d0 (some N) :- e L, len L N` constructs terms from a finite set. */
  private def unmeasuredConstructive(ctx: Ctx, allowed: RelSym => Boolean, answers: Boolean = false): Option[TerminationFailure] =
    val grows: RelSym => Boolean = x => inC(x) && !(answers && ctx.measuredAnywhere(x))
    rules.iterator.collectFirst(Function.unlift { r =>
      headRel(r).filterNot(allowed).flatMap(h =>
        phase.constructive(r, grows).map((why, sp) =>
          TerminationFailure(
            s"constructive rule for `${h.name}`, which has no measure",
            sp,
            why,
            Some(r),
            ctx.measures.keys.headOption.flatMap(ctx.directive),
            notes = List(s"`${h.name}` is in the recursive component ${showComponent(comp)}"),
            helps = List(s"give `${h.name}` a `%terminates` measure with the same shape, or mark it `%partial ${h.name}.`")
          )
        )
      )
    })

  /** Variables of `body` with finitely many values whatever the facts of the component: bound by positive
   *  atoms of finite sources outside the component ([[Termination.finiteVars]]), occurring in a column of `finite` of an
   *  atom of the component, or equal to a term over such variables. */
  private def finiteSources(body: List[Formula], finite: Set[(RelSym, Int)]): Set[String] =
    var vars = finiteVars(body, inC) ++ body.collect {
      case Formula.Atom(RelRef.Sym(x), as, _) if inC(x) =>
        as.zipWithIndex.collect { case (a, k) if finite((x, k)) => Moding.vars(a) }.flatten.toSet
    }.flatten.toSet
    var changed = true
    while changed do
      changed = false
      body.foreach {
        case Formula.Cmp(CmpOp.Eq, l, r) =>
          for (a, b) <- List((l, r), (r, l)) do
            a match
              case Term.Var(x) if !vars(x) && Moding.vars(b).subsetOf(vars) =>
                vars += x
                changed = true
              case _ =>
        case _ =>
      }
    vars

  /** The columns of unmeasured plain relations of the component whose values come from a finite set over
   *  the whole evaluation (a least fixed point): every rule of the relation puts into the column a term
   *  over variables of [[finiteSources]] (given the columns found so far). A column value is a function
   *  of the valuation of those variables, each of which ranges over a finite set. */
  private def finiteColumns(measured: RelSym => Boolean): Set[(RelSym, Int)] =
    val byHead = rules.groupBy(headRel).collect {
      case (Some(u), rs) if inC(u) && u.kind == RelKind.Plain && !measured(u) => u -> rs
    }
    var finite = Set.empty[(RelSym, Int)]
    var changed = true
    while changed do
      changed = false
      for (u, rs) <- byHead; k <- 0 until u.arity if !finite((u, k)) do
        val ok = rs.forall { r =>
          r.heads match
            case List(Term.App(_, hs)) => hs.lift(k).exists(h => Moding.vars(h).subsetOf(finiteSources(r.body, finite)))
            case _ => false
        }
        if ok then
          finite += ((u, k))
          changed = true
    finite

  /** Positive atoms of finite sources outside the component bind their variables to finitely many values
   *  (see [[Termination.finiteVars]]). */
  private def boundOutside(body: List[Formula]): Set[String] = finiteVars(body, inC)

  /** Bottom-up evaluation: every recursive call is smaller than the head and anchored. */
  private def bottomUp(ctx: Ctx): Either[TerminationFailure, List[String]] =
    unmeasuredConstructive(ctx, ctx.has).toLeft(()).flatMap { _ =>
      val lines = List.newBuilder[String]
      lines += "  bottom-up: each recursive call is smaller than the head; the call's measure lies in a finite set"
      val failure = rules.iterator.filter(r => headRel(r).exists(ctx.has)).flatMap { r =>
        val c = headRel(r).get
        val Term.App(_, hs) = r.heads.head: @unchecked
        val arith = Arithmetic(r.body)
        val outside = boundOutside(r.body)
        r.body.iterator.collect { case a @ Formula.Atom(RelRef.Sym(d), _, _) if inC(d) => (a, d) }.map { (a, d) =>
          if !ctx.has(d) then Some(unmeasuredCall(ctx, r, c, a, d))
          else
            val big = ctx.of(c).map(hs)
            val small = ctx.of(d).map(a.args)
            compare(ctx.slots, big, small, arith, r.body) match
              case Left(f) => Some(decreaseFailure(ctx, r, c, d, a.span, big, small, f, "the call", "the head"))
              case Right((i, why)) =>
                val anchors = (i until ctx.slots.length).toList.map { j =>
                  anchor(ctx.slots(j), j == i, big(j), small(j), arith, outside).toRight(j)
                }
                anchors.collectFirst { case Left(j) => j } match
                  case Some(j) => Some(anchorFailure(ctx, r, c, a.span, j, i, big(j), small(j)))
                  case None =>
                    val as = anchors.collect { case Right(s) => s }.mkString("; ")
                    lines += s"  ${where(r)}: call `${ObjPrinter.formula(a)}`: $why; anchored: $as"
                    None
        }
      }.collectFirst { case Some(f) => f }
      failure.toLeft(lines.result())
    }

  /** Whether the head's slot `h` (of call slot `s`) lies in a finite set (bottom-up anchor). The slot that
   *  increases only needs an upper bound: since the slots before it are unchanged, it does not decrease
   *  from the start of the chain. Later slots may be reset, so they need both bounds. */
  private def anchor(numeric: Boolean, increasing: Boolean, h: Term, s: Term, arith: Arithmetic, outside: Set[String]): Option[String] =
    def sh(t: Term) = ObjPrinter.term(t)
    def finiteVars(t: Term) = Moding.vars(t).subsetOf(outside)
    def bounded(iv: Interval) = iv.hi.isDefined && (increasing || iv.lo.isDefined)
    def outsideWhy(t: Term) =
      if Moding.vars(t).isEmpty then s"`${sh(t)}` is constant" else s"`${sh(t)}` is bound by relations outside the component"
    if finiteVars(h) then Some(outsideWhy(h))
    else if !numeric then None
    else
      val ih = arith(h)
      val shown = if increasing then Interval(None, ih.hi) else ih
      if bounded(ih) then Some(s"`${sh(h)}` ${shown.show}")
      else
        // the head is the call plus a bounded offset, and the call is bounded
        val d = arith.difference(h, s)
        val is = arith(s)
        if !bounded(d) then None
        else if finiteVars(s) then Some(s"${outsideWhy(s)} and `${sh(h)} - ${ObjPrinter.arg(s)}` ${d.show}")
        else if bounded(is) then
          Some(s"`${sh(s)}` ${(if increasing then Interval(None, is.hi) else is).show} and `${sh(h)} - ${ObjPrinter.arg(s)}` ${d.show}")
        else None

  /** Demand-driven evaluation: every demand is smaller than the demand guarding it, and integer slots
   *  are bounded below where they decrease. */
  private def moded(ctx: Ctx): Either[TerminationFailure, List[String]] =
    def demandOf(x: RelSym): Option[RelSym] = x.kind match
      case RelKind.Demand(of, _) if ctx.has(of) => Some(of)
      case _ => None
    // relations and demands of the other groups of the component (their own group checks them)
    def otherGroup(x: RelSym): Boolean = !ctx.has(x) && ctx.measuredAnywhere(x) || (x.kind match
      case RelKind.Demand(of, _) => !ctx.has(of) && ctx.measuredAnywhere(of)
      case _ => false
    )
    val measured = ctx.measures.keys.toList.sortBy(_.name)
    val unmoded = measured.find(!facts.hasModes(_)).map { c =>
      val other = measured.find(facts.hasModes).get
      TerminationFailure(
        s"`${c.name}` has a measure but no `%mode`",
        ctx.directive(c).getOrElse(c.span),
        "measure declared here",
        None,
        None,
        notes = List(s"`${other.name}` in the same component is moded, so the component is evaluated by demand"),
        helps = List(s"declare a mode for `${c.name}`, e.g. `%mode ${c.name} ${Mode(Vector.fill(c.arity)(true)).show}.`")
      )
    }
    val notInput = measured.iterator.flatMap(c =>
      facts.modes(c).iterator.flatMap((m, sp) => ctx.of(c).find(k => !m.inputs.lift(k).contains(true)).map(k => (c, m, sp, k)))
    ).nextOption().map { (c, m, sp, k) =>
      TerminationFailure(
        s"invalid `%terminates` directive for `${c.name}`",
        sp,
        s"argument ${k + 1} is not an input of mode ${m.show}",
        None,
        ctx.directive(c),
        notes = List("in a moded component the measure is checked on the demands, which consist of the input arguments")
      )
    }
    unmoded.orElse(notInput).orElse(
      unmeasuredConstructive(ctx, h => ctx.has(h) || demandOf(h).isDefined || otherGroup(h), answers = true)
    ).toLeft(()).flatMap {
      _ =>
        val lines = List.newBuilder[String]
        lines += "  demand-driven: each demand is smaller than the demand guarding it; decreasing integers are bounded below"
        // Rules of measured relations may call unmeasured relations of the component only if those do not
        // read answers of measured relations (except through demands): their facts are then determined by
        // the demands. Otherwise answers could feed themselves without any demand (`d X Z :- c X Z`).
        val calls = rules.iterator.filter(r => headRel(r).exists(ctx.has)).flatMap { r =>
          r.body.collectFirst(Function.unlift {
            case a @ Formula.Atom(RelRef.Sym(d), _, _) if inC(d) && !ctx.has(d) && demandOf(d).isEmpty && !otherGroup(d) =>
              readsAnswers(d, ctx.measuredAnywhere, x => demandOf(x).isDefined || otherGroup(x))
                .map(m => unmeasuredCall(ctx, r, headRel(r).get, a, d, Some(m)))
            case _ => None
          })
        }.nextOption()
        // Demand rules guarded by a demand of a measured relation, wherever they are (the demands of a
        // relation may form a component of their own, `log2^d H :- log2^d N, H = N / 2`), and the
        // demand rules of this component that read it (whose guard must then be measured).
        def guardOf(r: Rule) = r.body.collectFirst { case Formula.Atom(RelRef.Sym(x), _, _) if x.isDemand => x }
        def isDemandRule(r: Rule) = headRel(r).exists(h => demandOf(h).isDefined)
        val demandRules = (rules.filter(r =>
          isDemandRule(r) && r.body.exists {
            case Formula.Atom(RelRef.Sym(x), _, _) => inC(x)
            case _ => false
          }
        ) ++ allRules.filter(r => isDemandRule(r) && guardOf(r).exists(g => demandOf(g).isDefined))).distinct
        // A seed of the component: a demand rule without guard, or guarded by a demand of a relation
        // outside the component, that reads the component. The moded relation is then called from a rule
        // whose prefix reads relations depending on its answers (`d0 X :- e L X, len L N` and
        // `d2 N :- d0 X, f L X, len L N`). Its demands are finitely many if every input comes from a
        // finite set, independently of the component's facts.
        lazy val finiteCols = finiteColumns(ctx.measuredAnywhere)
        def seed(r: Rule, us: List[Term], e: RelSym): Option[TerminationFailure] =
          val finite = finiteSources(r.body, finiteCols)
          us.find(u => !Moding.vars(u).subsetOf(finite)) match
            case None =>
              lines += s"  ${where(r)}: demand `${ObjPrinter.term(r.heads.head)}` from outside the component: its inputs take finitely many values"
              None
            case Some(u) =>
              Some(TerminationFailure(
                s"invalid `%terminates` directive for `${e.name}`",
                u.span,
                s"the demanded `${ObjPrinter.term(u)}` may take infinitely many values",
                Some(r),
                ctx.directive(e),
                notes = List(
                  s"this call demands `${e.name}` with values read from relations that depend on the answers of `${e.name}`, so the demands could grow without bound"
                ),
                helps = List(s"bind the argument by a relation that does not depend on the answers of `${e.name}`", partialHelp(e))
              ))
        val demands = demandRules.iterator.flatMap { r =>
          val Term.App(RelRef.Sym(dh), us) = r.heads.head: @unchecked
          val e = demandOf(dh).get
          val guard = r.body.collectFirst { case g @ Formula.Atom(RelRef.Sym(x), _, _) if x.isDemand => g }
          guard match
            case Some(Formula.Atom(RelRef.Sym(dg), _, _)) if !inC(dg) && demandOf(dg).isEmpty && !otherGroup(dg) => seed(r, us, e)
            case Some(g @ Formula.Atom(RelRef.Sym(dg), ws, _)) =>
              demandOf(dg) match
                case None if otherGroup(dg) => None // a call between groups: ordered by the demand graph
                case None =>
                  val gOf = dg.kind match
                    case RelKind.Demand(of, _) => of
                    case _ => dg
                  Some(unmeasuredCall(ctx, r, gOf, g, gOf))
                case Some(c) =>
                  val arith = Arithmetic(r.body)
                  val outside = boundOutside(r.body)
                  val (ki, kg) = (inputPositions(dh, e, ctx.of(e)), inputPositions(dg, c, ctx.of(c)))
                  val small = ki.map(us)
                  val big = kg.map(ws)
                  compare(ctx.slots, big, small, arith, r.body) match
                    case Left(f) =>
                      Some(decreaseFailure(ctx, r, c, e, r.heads.head.span, big, small, f, "the call", "the caller"))
                    case Right((i, why)) =>
                      val u = small(i)
                      val lower =
                        if !ctx.slots(i) then Some("")
                        else if Moding.vars(u).subsetOf(outside) then
                          Some(s"; `${ObjPrinter.term(u)}` is bound by relations outside the component")
                        else arith(u).lo.map(b => s"; `${ObjPrinter.term(u)}` >= $b")
                      lower match
                        case Some(l) =>
                          lines += s"  ${where(r)}: demand for `${ObjPrinter.term(r.heads.head)}` from `${ObjPrinter.formula(g)}`: $why$l"
                          None
                        case None => Some(lowerBoundFailure(ctx, r, e, r.heads.head.span, i, u))
            case _ => seed(r, us, e)
        }.nextOption()
        calls.orElse(demands).toLeft(lines.result())
    }

  /** The positions of the measured arguments among the inputs of a demand relation. */
  private def inputPositions(d: RelSym, c: RelSym, ks: List[Int]): List[Int] = d.kind match
    case RelKind.Demand(_, m) => ks.map(k => m.inputs.take(k).count(identity))
    case _ => ks

  /** How `small` compares to `big` (Left: the first slot that is neither equal nor smaller, or None if all
   *  are equal), or the slot that decreases with an explanation. */
  private def compare(
      slots: List[Boolean],
      big: List[Term],
      small: List[Term],
      arith: Arithmetic,
      body: List[Formula]
  ): Either[Option[Int], (Int, String)] =
    val n = slots.length
    def go(i: Int, equal: List[String]): Either[Option[Int], (Int, String)] =
      if i == n then Left(None)
      else
        val (b, s) = (big(i), small(i))
        val eqWhy =
          if b == s then Some(s"`${ObjPrinter.term(s)}` unchanged")
          else if slots(i) then
            val d = arith.difference(b, s)
            if d.lo.contains(0) && d.hi.contains(0) then Some(s"`${ObjPrinter.term(s)}` = `${ObjPrinter.term(b)}`") else None
          else if body.exists {
              case Formula.Cmp(CmpOp.Eq, l, r) => (l == b && r == s) || (l == s && r == b)
              case _ => false
            }
          then Some(s"`${ObjPrinter.term(s)}` = `${ObjPrinter.term(b)}`")
          else None
        eqWhy match
          case Some(w) if n > 1 => go(i + 1, equal :+ w)
          case Some(_) => Left(None)
          case None =>
            val lt = if slots(i) then numericSmaller(b, s, arith) else structurallySmaller(b, s, body)
            lt match
              case Some(w) =>
                val prefix = if equal.isEmpty then "" else equal.mkString("", ", ", ", ")
                Right((i, prefix + w))
              case None => Left(Some(i))
    go(0, Nil)

  /** `s < b` for integers: the body implies `b - s >= 1`, or `s = x / l` with `l >= 2`, `x <= b`, `x >= 1`. */
  private def numericSmaller(b: Term, s: Term, arith: Arithmetic): Option[String] =
    val d = arith.difference(b, s)
    def sh(t: Term) = ObjPrinter.term(t)
    if d.lo.exists(_ >= 1) then Some(s"`${sh(b)} - ${ObjPrinter.arg(s)}` ${d.show}")
    else
      (s :: arith.definitions(s)).collectFirst(Function.unlift {
        case q @ Term.Arith(ArithOp.Div, x, IntLit(l))
            if l >= 2 && arith.difference(b, x).lo.exists(_ >= 0) && arith(x).lo.exists(_ >= 1) =>
          Some(s"`${sh(s)}` = `${sh(q)}` < `${sh(b)}` (`${sh(x)}` >= 1)")
        case _ => None
      })

  /** `s` is a proper subterm of `b`; variables of `b` bound to patterns (`P as V`, `V = c ...`) are unfolded. */
  private def structurallySmaller(b: Term, s: Term, body: List[Formula]): Option[String] =
    def defs(v: String): List[Term] =
      def inTerm(t: Term): List[Term] = t match
        case Term.As(x, `v`) => List(x)
        case Term.As(x, _) => inTerm(x)
        case Term.App(_, as) => as.flatMap(inTerm)
        case Term.Ascr(x, _) => inTerm(x)
        case _ => Nil
      body.flatMap {
        case Formula.Atom(r, as, Some(`v`)) => Term.App(r, as)(Span.NoSpan) :: as.flatMap(inTerm)
        case Formula.Atom(_, as, _) => as.flatMap(inTerm)
        case Formula.Cmp(CmpOp.Eq, Term.Var(`v`), a: Term.App) => List(a)
        case Formula.Cmp(CmpOp.Eq, a: Term.App, Term.Var(`v`)) => List(a)
        case _ => Nil
      }
    def inside(t: Term, depth: Int): Boolean = t match
      case Term.App(_, as) => as.exists(a => a == s || inside(a, depth))
      case Term.As(x, _) => inside(x, depth)
      case Term.Ascr(x, _) => inside(x, depth)
      case Term.Var(v) if depth > 0 => defs(v).exists(inside(_, depth - 1))
      case _ => false
    def unwrap(t: Term): Term = t match
      case Term.As(x, _) => unwrap(x)
      case Term.Ascr(x, _) => unwrap(x)
      case _ => t
    if inside(unwrap(b), 3) then Some(s"`${ObjPrinter.term(s)}` is a proper subterm of `${ObjPrinter.term(b)}`") else None

  /** A measured relation that `d` depends on inside the component, not counting dependencies through
   *  demand relations, with the path. */
  private def readsAnswers(d: RelSym, measured: RelSym => Boolean, demand: RelSym => Boolean): Option[List[RelSym]] =
    val succ = es.filter(e => inC(e.from) && inC(e.to)).groupMap(_.from)(_.to)
    val prev = scala.collection.mutable.HashMap(d -> d)
    var frontier = List(d)
    var hit: Option[RelSym] = None
    while frontier.nonEmpty && hit.isEmpty do
      frontier =
        for
          x <- frontier
          y <- succ.getOrElse(x, Nil).distinct
          if !prev.contains(y)
        yield
          prev(y) = x
          if measured(y) && hit.isEmpty then hit = Some(y)
          y
      frontier = frontier.filterNot(y => demand(y) || measured(y))
    hit.map { m =>
      var path = List(m)
      while path.head != d do path = prev(path.head) :: path
      path
    }

  private def unmeasuredCall(
      ctx: Ctx,
      r: Rule,
      c: RelSym,
      a: Formula.Atom,
      d: RelSym,
      reads: Option[List[RelSym]] = None
  ): TerminationFailure =
    val dependency =
      reads.map(p => s"`${d.name}` depends on the answers of `${p.last.name}`: ${p.map(x => s"`${x.name}`").mkString(" -> ")}")
    TerminationFailure(
      s"`${c.name}` calls `${d.name}`, which has no measure",
      a.span,
      s"`${d.name}` is in the same recursive component",
      Some(r),
      ctx.directive(c),
      notes = s"the component is ${showComponent(comp)}; a measure must decrease along every recursive call" :: dependency.toList,
      helps = List(s"give `${d.name}` a `%terminates` measure with the same shape as `${c.name}`'s")
    )

  private def decreaseFailure(
      ctx: Ctx,
      r: Rule,
      c: RelSym,
      d: RelSym,
      span: Span,
      big: List[Term],
      small: List[Term],
      slot: Option[Int],
      smallWhat: String,
      bigWhat: String
  ): TerminationFailure =
    val n = ctx.slots.length
    def sh(ts: List[Term]) = if n == 1 then s"`${ObjPrinter.term(ts.head)}`" else ts.map(ObjPrinter.term).mkString("`(", ", ", ")`")
    val label = slot match
      case None => s"no decrease: ${sh(small)} is not smaller than ${sh(big)}"
      case Some(i) =>
        val which = if n == 1 then "" else s"component ${i + 1} of the measure: "
        val b = ObjPrinter.term(big(i))
        val s = ObjPrinter.term(small(i))
        if ctx.slots(i) then s"no decrease: ${which}cannot show `$s < $b`"
        else s"no decrease: ${which}`$s` is not a proper subterm of `$b`"
    val measure = if n == 1 then "the measure" else "the lexicographic measure"
    val help = slot match
      case Some(i) if ctx.slots(i) && Moding.vars(small(i)).nonEmpty =>
        List(
          s"the body must imply `${ObjPrinter.term(big(i))} - ${ObjPrinter.arg(small(i))} >= 1`, e.g. through `${ObjPrinter.term(small(i))} = ${ObjPrinter.term(big(i))} - 1`"
        )
      case Some(i) if !ctx.slots(i) =>
        List("a recursive call must take a component of the matched argument, as in `len (cons X L) ... :- ..., len L N`")
      case _ => Nil
    TerminationFailure(
      s"invalid `%terminates` directive for `${d.name}`",
      span,
      label,
      Some(r),
      ctx.directive(d),
      secondary = List(big(slot.getOrElse(0)).span -> s"$bigWhat has `${ObjPrinter.term(big(slot.getOrElse(0)))}`"),
      notes = List(
        s"$measure of `${d.name}` is ${showPositions(d, ctx.of(d))}; for $smallWhat it must be smaller than for $bigWhat"
      ),
      helps = help :+ partialHelp(d)
    )

  private def anchorFailure(ctx: Ctx, r: Rule, c: RelSym, span: Span, j: Int, i: Int, h: Term, s: Term): TerminationFailure =
    val (hs, ss) = (ObjPrinter.term(h), ObjPrinter.term(s))
    val which = if ctx.slots.length == 1 then "" else s"component ${j + 1} of the measure: "
    val (label, help) =
      if ctx.slots(j) && j == i then
        (s"no anchor: ${which}the body bounds neither `$hs` nor `$ss` from above", s"add an upper bound, e.g. `$ss < 100`")
      else if ctx.slots(j) then
        (
          s"no anchor: ${which}the body does not bound `$hs` from above and below",
          s"add bounds, e.g. `$ss >= 0, $ss < 100`; a component after the increasing one can change arbitrarily"
        )
      else
        (
          s"no anchor: ${which}the variables of `$hs` are not bound by a relation outside the component",
          s"match the head's argument against existing facts, e.g. `len (cons X L) M :- cons X L, len L N, ...`"
        )
    TerminationFailure(
      s"invalid `%terminates` directive for `${c.name}`",
      span,
      label,
      Some(r),
      ctx.directive(c),
      secondary = List(h.span -> s"the head has `$hs`"),
      notes = List("bottom-up, the measure grows from the call to the head; it must stay in a finite set for the recursion to stop"),
      helps = List(help, partialHelp(c))
    )

  private def lowerBoundFailure(ctx: Ctx, r: Rule, e: RelSym, span: Span, i: Int, u: Term): TerminationFailure =
    val sh = ObjPrinter.term(u)
    val which = if ctx.slots.length == 1 then "" else s"component ${i + 1} of the measure: "
    TerminationFailure(
      s"invalid `%terminates` directive for `${e.name}`",
      span,
      s"no anchor: ${which}the body does not bound the demanded `$sh` from below",
      Some(r),
      ctx.directive(e),
      notes = List("demands decrease from caller to callee; integers must stay bounded below for the recursion to stop"),
      helps = List(s"add a lower bound, e.g. `$sh >= 0`, or bound the caller's argument (`N > 0` with `$sh = N - 1`)", partialHelp(e))
    )

  private def partialHelp(c: RelSym): String =
    s"if the recursion terminates for another reason, mark the relation `%partial ${c.name}.` to evaluate it with a round budget"

  private def where(r: Rule): String = s"rule at ${r.span.show}"

object Termination:
  def headRel(r: Rule): Option[RelSym] = r.heads.headOption.collect { case Term.App(RelRef.Sym(c), _) => c }

  /** The relation a demand relation belongs to, or the relation itself. */
  def base(c: RelSym): RelSym = c.kind match
    case RelKind.Demand(of, _) => of
    case _ => c

  /** Variables of `body` bound by positive atoms of relations outside the component `inC` that are finite
   *  sources: complete and finite when the component is evaluated (induction over the evaluation order).
   *  Fact constructors and fact structs are finite sources too: a nested head term `c t̄` asserted by a
   *  rule of a later component is also derived by its split rule in `c`'s component (Proposition 8.8,
   *  `StratifyPhase.splitRules`), so no fact is added to `c` after its component (`d (s (s N)) :- s N`
   *  is split into `s (s N) :- s N`, which is checked in `s`'s component). A data constructor has no
   *  facts; an atom over it is a generated guard `(c Z̄ as X)` destructuring the value of `X`, so its
   *  variables are finite if `X` is. */
  def finiteVars(body: List[Formula], inC: RelSym => Boolean): Set[String] =
    var vars = body.collect {
      case Formula.Atom(RelRef.Sym(x), as, v) if !inC(x) && !x.isData => as.flatMap(Moding.vars).toSet ++ v
    }.flatten.toSet
    val guards = body.collect { case Formula.Atom(RelRef.Sym(x), as, Some(v)) if x.isData => (v, as.flatMap(Moding.vars).toSet) }
    var changed = true
    while changed do
      changed = false
      for (v, inner) <- guards if vars(v) && !inner.subsetOf(vars) do
        vars ++= inner
        changed = true
    vars

  def showComponent(comp: List[RelSym]): String = comp.map(_.name).mkString("{", ", ", "}")

  def isInt(t: OType): Boolean = t match
    case OType.Int => true
    case OType.Con(s, _) =>
      s.kind match
        case TypeKind.Refinement(base) => isInt(base)
        case _ => false
    case _ => false

  def plural(n: Int): String = if n == 1 then "1 argument" else s"$n arguments"

  def kind(numeric: Boolean): String = if numeric then "an integer" else "a term"

  def showPositions(c: RelSym, ks: List[Int]): String =
    ks.map(k =>
      s"argument ${k + 1}${c.cols.lift(k).flatMap(_.label).map(l => s" `$l`")
          .getOrElse("")} (${if c.cols.lift(k).exists(col => isInt(col.tpe)) then "integer" else "structural"})"
    )
      .mkString(", ")

  /** A `%terminates` directive for the measure `ks` of `c`. */
  def directive(c: RelSym, ks: List[Int]): String =
    val labels = ks.map(k => c.cols.lift(k).flatMap(_.label))
    if labels.forall(_.isDefined) then s"`%terminates ${hugin.syntax.Printer.measure(labels.flatten)} ${c.name}.`"
    else
      val names = ks.zipWithIndex.map((k, i) => k -> (if ks.length == 1 then "X" else s"X${i + 1}")).toMap
      val pat = (0 until c.arity).map(k => names.getOrElse(k, "_")).mkString(" ")
      s"`%terminates ${hugin.syntax.Printer.measure(ks.map(names))} (${c.name} $pat).`"
