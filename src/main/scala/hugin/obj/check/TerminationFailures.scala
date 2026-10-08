package hugin.obj
package check

import hugin.util.*
import hugin.util.diagnostics.{Code, Legacy}
import hugin.compiler.*

import hugin.obj.typing.Moding

/** What a [[TerminationFailure]] is about: a missing decrease, a missing bound, or anything else. */
enum FailKind:
  case Decrease, Anchor, Other

/** A violation of the termination conditions, with everything the diagnostic shows. */
final case class TerminationFailure(
    message: String,
    span: Span,
    label: String,
    rule: Option[Rule],
    directive: Option[Span],
    secondary: List[(Span, String)] = Nil,
    notes: List[String] = Nil,
    helps: List[String] = Nil,
    kind: FailKind = FailKind.Other,
    measure: String = ""
):
  def diagnostic: Diagnostic =
    var d = Legacy.error(Code.E0604, message, span, label)
    for (s, l) <- secondary if s.exists do d = d.withLabel(s, l)
    for s <- directive if s.exists do d = d.withLabel(s, "measure declared here")
    notes.foreach(n => d = d.withNote(n))
    helps.foreach(h => d = d.withHelp(h))
    rule.map(r => Diag.rule(r)(d)).getOrElse(d)

/** The diagnostics of the termination check. */
object Failures:
  import Termination.*

  /** E0603: a growing component for which neither direction of the size-change criterion holds
   *  (docs/REDESIGN.md §4.4): the invention site, the cycle, why each direction fails, and a help. */
  def noMeasure(rc: RecursiveComponent, induction: GuardedInduction, descent: SizeChange.Failure, r: Rule, why: String, sp: Span)(
      using Context
  ): Diagnostic =
    val comp = rc.comp
    var d = Legacy.error(Code.E0603, "growing component without a termination argument", sp, why)
      .withNote(
        s"the recursive component ${Termination.showComponent(comp)} contains this constructive rule, so its fixed point may be infinite"
      )
    Termination.headRel(r).flatMap(rc.cycle).foreach(c => d = d.withNote(s"recursion: ${c.map(x => s"`${x.name}`").mkString(" -> ")}"))
    if ctx.unit.splitRules.contains(r) then
      Termination.headRel(r).foreach(c =>
        d = d.withNote(
          s"the rule asserts the fact `${ObjPrinter.term(r.heads.head)}` of `${c.name}`, so it is also evaluated in `${c.name}`'s component"
        )
      )
    descent.chain match
      case Some(c) =>
        val via = c.steps.map(s => s"rule at ${s.rule.span.show}").distinct.mkString(", ")
        d = d.withNote(
          s"descent along derivations (A) fails: along `${c.from.name}` -> ... -> `${c.to.name}` ($via) no argument of the derived fact is smaller than in the premise"
        )
      case None =>
        d = d.withNote("descent along derivations (A) fails: the size-change graphs of the component are too many to check")
    d = d.withNote(s"guarded induction (B) fails: ${induction.inductionFailure}")
    val hints = descent.chain.toList.flatMap(_.steps.flatMap(_.hints)).distinct
    hints.headOption match
      case Some(SizeChange.Hint(_, h, s, up)) =>
        val (hs, ss) = (ObjPrinter.term(h), ObjPrinter.term(s))
        val guard = if up then s"`$hs < 100`" else s"`$hs >= 0`"
        d.withHelp(
          s"`$hs` is ${if up then "larger" else "smaller"} than `$ss` but not bounded ${if up then "above" else "below"}: add a guard such as $guard (or bound `$ss`)"
        )
      case None =>
        val names = comp.map(Termination.base).filter(c => c.kind == RelKind.Plain || DepGraph.isFactCtor(c)).distinct.map(_.name)
        d.withHelp(names.headOption.map(n =>
          s"make an argument decrease along the recursion (a proper subterm, or an integer bounded by a guard such as `N > 0`), or name the measure with `%terminates X ($n ...)`"
        ).getOrElse("make an argument decrease along the recursion (a proper subterm, or an integer bounded by a guard such as `N > 0`)"))

  /** What a [[TerminationFailure]] is about: a missing decrease, a missing bound, or anything else. */
  def unmeasuredCall(
      ctx: MeasureCtx,
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
      notes = s"the component is ${showComponent(ctx.comp)}; a measure must decrease along every recursive call" :: dependency.toList,
      helps = List(s"give `${d.name}` a `%terminates` measure with the same shape as `${c.name}`'s")
    )

  def decreaseFailure(
      ctx: MeasureCtx,
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
      helps = help,
      kind = FailKind.Decrease,
      measure = showPositions(d, ctx.of(d))
    )

  def anchorFailure(ctx: MeasureCtx, r: Rule, c: RelSym, span: Span, j: Int, i: Int, h: Term, s: Term): TerminationFailure =
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
      helps = List(help),
      kind = FailKind.Anchor,
      measure = showPositions(c, ctx.of(c))
    )

  def lowerBoundFailure(ctx: MeasureCtx, r: Rule, e: RelSym, span: Span, i: Int, u: Term): TerminationFailure =
    val sh = ObjPrinter.term(u)
    val which = if ctx.slots.length == 1 then "" else s"component ${i + 1} of the measure: "
    TerminationFailure(
      s"invalid `%terminates` directive for `${e.name}`",
      span,
      s"no anchor: ${which}the body does not bound the demanded `$sh` from below",
      Some(r),
      ctx.directive(e),
      notes = List("demands decrease from caller to callee; integers must stay bounded below for the recursion to stop"),
      helps = List(s"add a lower bound, e.g. `$sh >= 0`, or bound the caller's argument (`N > 0` with `$sh = N - 1`)"),
      kind = FailKind.Anchor,
      measure = showPositions(e, ctx.of(e))
    )

  def where(r: Rule): String = s"rule at ${r.span.show}"
