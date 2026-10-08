package hugin.obj
package check

import hugin.util.*

import hugin.obj.typing.Moding

/** The measures of one group of a component (see [[GuardedInduction.check]]): `slots` says which slots
 *  are integers, `all` are the measures of the whole component. */
final case class MeasureCtx(
    measures: Map[RelSym, List[Int]],
    slots: List[Boolean],
    all: Map[RelSym, List[Int]],
    facts: ProgramFacts,
    comp: List[RelSym]
):
  def of(c: RelSym): List[Int] = measures(c)
  def has(c: RelSym): Boolean = measures.contains(c)

  /** Measured in the component, possibly in another group (see [[GuardedInduction.check]]). */
  def measuredAnywhere(c: RelSym): Boolean = all.contains(c)
  def directive(c: RelSym): Option[Span] = facts(c).terminates.map(_._2)

  /** The measure of `c` in this group. */
  def measure(c: RelSym): Measure = Measure(c, of(c), slots)

/** Guarded induction (B): measures, declared or inferred, that decrease from the head to every recursive
 *  call and are anchored in a finite set. */
final class GuardedInduction(rc: RecursiveComponent):
  import Termination.*
  import Decrease.*

  private val (comp, rules, allRules, facts) = (rc.comp, rc.rules, rc.allRules, rc.facts)
  private val inC = rc.inC

  /** The candidate measures of the inference for guarded induction (B): one integer or structural argument
   *  per relation, or a lexicographic pair for a single relation. */
  private def candidates: Iterator[Map[RelSym, List[Int]]] =
    val rels = comp.distinct.filter(c => c.kind == RelKind.Plain && c.arity > 0)
    def positions(c: RelSym) = (0 until c.arity - (if c.boundColumn.isDefined then 1 else 0)).toList
    val singles: Iterator[Map[RelSym, List[Int]]] =
      if rels.isEmpty || rels.length > 4 then Iterator.empty
      else
        rels.foldLeft(Iterator(Map.empty[RelSym, List[Int]]))((acc, c) =>
          acc.flatMap(m => positions(c).iterator.map(k => m.updated(c, List(k))))
        ).take(256)
    val pairs: Iterator[Map[RelSym, List[Int]]] = rels match
      case List(c) => for i <- positions(c).iterator; j <- positions(c).iterator if i != j yield Map(c -> List(i, j))
      case _ => Iterator.empty
    singles ++ pairs

  /** Guarded induction (B) with an inferred measure: the first candidate that passes [[check]]. */
  def infer: Option[(Map[RelSym, List[Int]], List[String])] =
    candidates.map(m => (m, check(m))).collectFirst { case (m, Right(lines)) =>
      val shown = m.toList.sortBy(_._1.name).map((c, ks) => directive(c, ks)).mkString(" ")
      (m, s"  inferred measure: $shown" :: lines)
    }

  /** Why guarded induction (B) fails, for E0603: the anchor failure of the first candidate measure that
   *  decreases along every recursive call but is not anchored; `None` if no argument decreases. */
  def inductionFailure: Option[TerminationError] =
    candidates.map(check).collectFirst { case Left(f) if f.error.isAnchor => f.error }

  /** Checks the component with the given measures; the explanation, or the first violation. */
  def check(measures: Map[RelSym, List[Int]]): Either[Rejection, List[String]] = checkGroup(measures, measures)

  /** Checks relations whose measures are compared with each other; `all` are the measures of the whole
   *  component. */
  def checkGroup(measures: Map[RelSym, List[Int]], all: Map[RelSym, List[Int]]): Either[Rejection, List[String]] =
    val measured = measures.keys.toList.sortBy(_.name)
    def declared(c: RelSym) = facts(c).terminates.map(_._2)
    val first = measured.head
    val n = measures(first).length
    def slotNumeric(c: RelSym, k: Int) = c.cols.lift(k).exists(col => isInt(col.tpe))
    val shapeError = measured.collectFirst {
      case c if measures(c).length != n =>
        val at = declared(c).getOrElse(c.span)
        Rejection(TerminationError.MeasureLengths(comp, c, measures(c).length, at, first, n, declared(first)), None)
      case c if (0 until n).exists(i => slotNumeric(c, measures(c)(i)) != slotNumeric(first, measures(first)(i))) =>
        val i = (0 until n).find(i => slotNumeric(c, measures(c)(i)) != slotNumeric(first, measures(first)(i))).get
        val (numeric, firstNumeric) = (slotNumeric(c, measures(c)(i)), slotNumeric(first, measures(first)(i)))
        val at = declared(c).getOrElse(c.span)
        Rejection(TerminationError.MeasureTypes(comp, c, i, numeric, at, first, firstNumeric, declared(first)), None)
    }
    val slots = (0 until n).toList.map(i => slotNumeric(first, measures(first)(i)))
    val ctx = MeasureCtx(measures, slots, all, facts, comp)
    shapeError.toLeft(()).flatMap { _ =>
      bottomUp(ctx)
    }.map { lines =>
      val ms = measured.map(c =>
        s"  measure of `${c.name}`: ${showPositions(c, measures(c))}${if n > 1 then " (lexicographic)" else ""}"
      )
      ms ++ lines
    }

  /** Bottom-up evaluation: every recursive call is smaller than the head and anchored. */
  def bottomUp(ctx: MeasureCtx): Either[Rejection, List[String]] =
    rc.unmeasuredConstructive(ctx, ctx.has).toLeft(()).flatMap { _ =>
      val lines = List.newBuilder[String]
      lines += "  guarded induction (B): each recursive call is smaller than the head; the head's measure lies in a finite set"
      val failure = rules.iterator.filter(r => headRel(r).exists(ctx.has)).flatMap { r =>
        val c = headRel(r).get
        val Term.App(_, hs) = r.heads.head: @unchecked
        val arith = Arithmetic(r.body)
        val outside = rc.boundOutside(r.body)
        r.body.iterator.collect { case a @ Formula.Atom(RelRef.Sym(d), _, _) if inC(d) => (a, d) }.map { (a, d) =>
          if !ctx.has(d) then Some(Rejection.unmeasuredCall(ctx, r, c, a, d))
          else
            val big = ctx.of(c).map(hs)
            val small = ctx.of(d).map(a.args)
            compare(ctx.slots, big, small, arith, r.body) match
              case Left(f) =>
                Some(Rejection(
                  TerminationError.NoDecrease(ctx.measure(d), a.span, big, small, f, Roles.CallAndHead, ctx.directive(d)),
                  Some(r)
                ))
              case Right((i, why)) =>
                val anchors = (i until ctx.slots.length).toList.map { j =>
                  anchor(ctx.slots(j), j == i, big(j), small(j), arith, outside).toRight(j)
                }
                anchors.collectFirst { case Left(j) => j } match
                  case Some(j) =>
                    val p = TerminationError.NoAnchor(ctx.measure(c), a.span, j, i, big(j), small(j), ctx.directive(c))
                    Some(Rejection(p, Some(r)))
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
  def anchor(numeric: Boolean, increasing: Boolean, h: Term, s: Term, arith: Arithmetic, outside: Set[String]): Option[String] =
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
