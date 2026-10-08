package hugin.obj
package check

import hugin.obj.DiagArgs.given
import hugin.obj.typing.Moding
import hugin.util.{Diagnostic, Span}
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** Problems of the termination check (E0603, E0604; docs/REDESIGN.md §4): a growing component without a
 *  termination argument, and the ways a measure of guarded induction (B), declared by `%terminates` or
 *  tried by the inference, can fail. Reasons are data (the invention site, the cycle, why each direction
 *  fails, the missing guard); the wording is here only.
 *
 *  `directive` fields hold the span of the `%terminates` directive of the measured relation, if one was
 *  declared; it gets the secondary label "measure declared here". */
enum TerminationError extends Problem:
  /** E0603: a recursive component with the constructive rule `invention` for which neither direction of
   *  the size-change criterion holds. `cycle` is the shortest recursion through the rule's head relation,
   *  `asserted` the fact a split rule (Proposition 8.8) asserts with the relation it belongs to,
   *  `induction` the failure of the first inferred measure that decreases but is not anchored, `guard` a
   *  bound that would make a step of (A) strict, and `measurable` a relation a `%terminates` could name. */
  case NoArgument(
      comp: List[RelSym],
      invention: Invention,
      cycle: Option[List[RelSym]],
      asserted: Option[(Term, RelSym)],
      descent: DescentFailure,
      induction: Option[TerminationError],
      guard: Option[MissingGuard],
      measurable: Option[RelSym]
  )

  /** `caller`, which has a measure, calls `callee` of its component, which has none; `reads` is the path
   *  by which `callee` depends on the answers of a measured relation (demand-driven components). */
  case UnmeasuredCall(
      caller: RelSym,
      callee: RelSym,
      at: Span,
      directive: Option[Span],
      comp: List[RelSym],
      reads: Option[List[RelSym]]
  )

  /** The measure is not smaller at `roles.small` (the terms `small`) than at `roles.big` (`big`); `slot` is
   *  the first component that is neither equal nor smaller, `None` if all are equal. */
  case NoDecrease(
      measure: Measure,
      at: Span,
      big: List[Term],
      small: List[Term],
      slot: Option[Int],
      roles: Roles,
      directive: Option[Span]
  )

  /** Bottom-up, component `slot` of the head's measure (`head`, from the call's `call`) does not lie in a
   *  finite set; `increasing` is the component that decreases from the head to the call. */
  case NoAnchor(measure: Measure, at: Span, slot: Int, increasing: Int, head: Term, call: Term, directive: Option[Span])

  /** Demand-driven, the integer component `slot` of a demand (`demanded`) decreases without a lower bound. */
  case UnboundedDemand(measure: Measure, at: Span, slot: Int, demanded: Term, directive: Option[Span])

  /** A demand of `rel` from outside the component reads values that depend on `rel`'s answers. */
  case InfiniteDemand(rel: RelSym, demanded: Term, directive: Option[Span])

  /** The measures of `rel` (declared at `at`) and `first` (at `firstAt`) have different lengths. */
  case MeasureLengths(comp: List[RelSym], rel: RelSym, length: Int, at: Span, first: RelSym, firstLength: Int, firstAt: Option[Span])

  /** Component `slot` of the measures of `rel` and `first` is an integer in one and a term in the other. */
  case MeasureTypes(
      comp: List[RelSym],
      rel: RelSym,
      slot: Int,
      numeric: Boolean,
      at: Span,
      first: RelSym,
      firstNumeric: Boolean,
      firstAt: Option[Span]
  )

  /** A rule of `rel`, which has no measure, is constructive (`invention`). */
  case UnmeasuredConstructive(rel: RelSym, invention: Invention, directive: Option[Span], comp: List[RelSym])

  def code: Code = this match
    case _: NoArgument => Code.E0603
    case _ => Code.E0604

  /** A failure to anchor the measure in a finite set (rather than to decrease it). */
  def isAnchor: Boolean = this match
    case _: NoAnchor | _: UnboundedDemand => true
    case _ => false

  def primary: Span = this match
    case p: NoArgument => p.invention.at
    case p: UnmeasuredCall => p.at
    case p: NoDecrease => p.at
    case p: NoAnchor => p.at
    case p: UnboundedDemand => p.at
    case p: InfiniteDemand => p.demanded.span
    case p: MeasureLengths => p.at
    case p: MeasureTypes => p.at
    case p: UnmeasuredConstructive => p.invention.at

  def message: Msg = this match
    case _: NoArgument => msg"growing component without a termination argument"
    case p: UnmeasuredCall => msg"${p.caller} calls ${p.callee}, which has no measure"
    case p: MeasureLengths => msg"measures of different lengths in the component ${component(p.comp)}"
    case p: MeasureTypes => msg"measures of different types in the component ${component(p.comp)}"
    case p: UnmeasuredConstructive => msg"constructive rule for ${p.rel}, which has no measure"
    case _ => msg"invalid `%terminates` directive for ${measured.get}"

  override def primaryLabel: Msg = this match
    case p: NoArgument => p.invention.describe
    case p: UnmeasuredCall => msg"${p.callee} is in the same recursive component"
    case p: NoDecrease => TerminationWording.noDecrease(p)
    case p: NoAnchor => TerminationWording.noAnchor(p)._1
    case p: UnboundedDemand =>
      msg"no anchor: ${p.measure.component(p.slot)}the body does not bound the demanded ${p.demanded} from below"
    case p: InfiniteDemand => msg"the demanded ${p.demanded} may take infinitely many values"
    case p: MeasureLengths => msg"${p.rel} is measured by ${Lit(Termination.plural(p.length))}"
    case p: MeasureTypes => msg"component ${p.slot + 1} of ${p.rel}'s measure is ${Lit(Termination.kind(p.numeric))}"
    case p: UnmeasuredConstructive => p.invention.describe

  /** The related places, then the `%terminates` directive; places without source text are dropped. */
  override def labels: List[(Span, Msg)] =
    val related = this match
      case p: NoDecrease =>
        val k = p.slot.getOrElse(0)
        List(p.big(k).span -> msg"${Lit(p.roles.big)} has ${p.big(k)}")
      case p: NoAnchor => List(p.head.span -> msg"the head has ${p.head}")
      case p: MeasureLengths => p.firstAt.toList.map(_ -> msg"${p.first} is measured by ${Lit(Termination.plural(p.firstLength))}")
      case p: MeasureTypes =>
        p.firstAt.toList.map(_ -> msg"component ${p.slot + 1} of ${p.first}'s measure is ${Lit(Termination.kind(p.firstNumeric))}")
      case _ => Nil
    (related ++ directive.toList.map(_ -> msg"measure declared here")).filter(_._1.exists)

  override def notes: List[Msg] = this match
    case p: NoArgument => TerminationWording.noArgumentNotes(p)
    case p: UnmeasuredCall =>
      msg"the component is ${component(p.comp)}; a measure must decrease along every recursive call" ::
        p.reads.toList.map(path => msg"${p.callee} depends on the answers of ${path.last}: ${arrows(path)}")
    case p: NoDecrease =>
      val m = p.measure
      val which = if m.lexicographic then "the lexicographic measure" else "the measure"
      List(msg"${Lit(which)} of ${m.rel} is ${m.positionsShown}; for ${Lit(p.roles.small)} it must be smaller than for ${Lit(p.roles.big)}")
    case _: NoAnchor =>
      List(msg"bottom-up, the measure grows from the call to the head; it must stay in a finite set for the recursion to stop")
    case _: UnboundedDemand => List(msg"demands decrease from caller to callee; integers must stay bounded below for the recursion to stop")
    case p: InfiniteDemand =>
      List(
        msg"this call demands ${p.rel} with values read from relations that depend on the answers of ${p.rel}, so the demands could grow without bound"
      )
    case _: MeasureLengths => List(msg"measures of mutually recursive relations are compared with each other, so they need the same shape")
    case _: MeasureTypes => Nil
    case p: UnmeasuredConstructive => List(msg"${p.rel} is in the recursive component ${component(p.comp)}")

  override def helps: List[Msg] = this match
    case p: NoArgument => List(TerminationWording.noArgumentHelp(p))
    case p: UnmeasuredCall => List(msg"give ${p.callee} a `%terminates` measure with the same shape as ${p.caller}'s")
    case p: NoDecrease => TerminationWording.decreaseHelp(p).toList
    case p: NoAnchor => List(TerminationWording.noAnchor(p)._2)
    case p: UnboundedDemand =>
      val u = ObjPrinter.term(p.demanded)
      List(msg"add a lower bound, e.g. ${Src(s"$u >= 0")}, or bound the caller's argument (`N > 0` with ${Src(s"$u = N - 1")})")
    case p: InfiniteDemand => List(msg"bind the argument by a relation that does not depend on the answers of ${p.rel}")
    case p: UnmeasuredConstructive => List(msg"give ${p.rel} a `%terminates` measure with the same shape")
    case _ => Nil

  /** The measured relation of a `%terminates` problem. */
  private def measured: Option[RelSym] = this match
    case p: NoDecrease => Some(p.measure.rel)
    case p: NoAnchor => Some(p.measure.rel)
    case p: UnboundedDemand => Some(p.measure.rel)
    case p: InfiniteDemand => Some(p.rel)
    case _ => None

  private def directive: Option[Span] = this match
    case p: UnmeasuredCall => p.directive
    case p: NoDecrease => p.directive
    case p: NoAnchor => p.directive
    case p: UnboundedDemand => p.directive
    case p: InfiniteDemand => p.directive
    case p: UnmeasuredConstructive => p.directive
    case _ => None

  private def component(comp: List[RelSym]): Lit = Lit(Termination.showComponent(comp))
  private def arrows(path: List[RelSym]): Msg = Msg.join(path.map(r => msg"$r"), " -> ")

/** The wording of the [[TerminationError]] cases whose text depends on the shape of the measure. */
private object TerminationWording:
  import TerminationError.*

  private def term(t: Term): String = ObjPrinter.term(t)

  def noArgumentNotes(p: NoArgument): List[Msg] =
    val invention =
      msg"the recursive component ${Lit(Termination.showComponent(p.comp))} contains this constructive rule, so its fixed point may be infinite"
    val cycle = p.cycle.map(c => msg"recursion: ${Msg.join(c.map(r => msg"$r"), " -> ")}")
    val asserted = p.asserted.map((t, c) => msg"the rule asserts the fact $t of $c, so it is also evaluated in $c's component")
    val induction = p.induction match
      case Some(a: (NoAnchor | UnboundedDemand)) =>
        val m = a match
          case n: NoAnchor => n.measure
          case u: UnboundedDemand => u.measure
        msg"guarded induction (B) fails: ${a.primaryLabel} (measure: ${m.positionsShown})"
      case _ => msg"guarded induction (B) fails: no argument decreases from the head to every recursive call"
    // a demand relation and the relation it is the demand of, in one component (C3, known limitation)
    val mixed = p.comp.collectFirst(Function.unlift(d =>
      d.derivedFrom.flatMap(b => p.comp.find(_.displayName == b)).map(b =>
        msg"the component mixes the demand relation $d, whose rules descend (A), with $b, whose rules are guarded by it (B): a demand that needs an answer of $b (an input bound by an earlier call) puts them in one component, and components mixing the two directions are not supported"
      )
    ))
    (invention :: cycle.toList) ++ asserted.toList ++ List(p.descent.note, induction) ++ mixed.toList

  def noArgumentHelp(p: NoArgument): Msg =
    val decrease = "make an argument decrease along the recursion (a proper subterm, or an integer bounded by a guard such as `N > 0`)"
    p.guard match
      case Some(g) => g.help
      case None =>
        p.measurable match
          case Some(r) => Msg.text(decrease) ++ msg", or name the measure with ${Src(s"%terminates X (${r.name} ...)")}"
          case None => Msg.text(decrease)

  /** The measure as written in a label: one term, or a tuple for a lexicographic measure. */
  private def shown(m: Measure, ts: List[Term]): Msg =
    if m.lexicographic then msg"${Src(ts.map(term).mkString("(", ", ", ")"))}" else msg"${ts.head}"

  def noDecrease(p: NoDecrease): Msg = p.slot match
    case None => msg"no decrease: ${shown(p.measure, p.small)} is not smaller than ${shown(p.measure, p.big)}"
    case Some(i) =>
      val which = p.measure.component(i)
      val (b, s) = (p.big(i), p.small(i))
      if p.measure.slots(i) then msg"no decrease: ${which}cannot show ${Src(s"${term(s)} < ${term(b)}")}"
      else msg"no decrease: $which$s is not a proper subterm of $b"

  def decreaseHelp(p: NoDecrease): Option[Msg] = p.slot match
    case Some(i) if p.measure.slots(i) && Moding.vars(p.small(i)).nonEmpty =>
      val (b, s) = (p.big(i), p.small(i))
      Some(msg"the body must imply ${Src(s"${term(b)} - ${ObjPrinter.arg(s)} >= 1")}, e.g. through ${Src(s"${term(s)} = ${term(b)} - 1")}")
    case Some(i) if !p.measure.slots(i) =>
      Some(msg"a recursive call must take a component of the matched argument, as in `len (cons X L) ... :- ..., len L N`")
    case _ => None

  /** The label and the help of a missing anchor. */
  def noAnchor(p: NoAnchor): (Msg, Msg) =
    val which = p.measure.component(p.slot)
    val (h, s) = (p.head, term(p.call))
    if p.measure.slots(p.slot) && p.slot == p.increasing then
      (msg"no anchor: ${which}the body bounds neither $h nor ${p.call} from above", msg"add an upper bound, e.g. ${Src(s"$s < 100")}")
    else if p.measure.slots(p.slot) then
      (
        msg"no anchor: ${which}the body does not bound $h from above and below",
        msg"add bounds, e.g. ${Src(s"$s >= 0, $s < 100")}; a component after the increasing one can change arbitrarily"
      )
    else
      (
        msg"no anchor: ${which}the variables of $h are not bound by a relation outside the component",
        msg"match the head's argument against existing facts, e.g. `len (cons X L) M :- cons X L, len L N, ...`"
      )

/** A violation of the termination conditions found while checking a component, with the rule it lies in
 *  (whose meta-level origin the diagnostic shows). */
final case class Rejection(error: TerminationError, rule: Option[Rule]):
  def diagnostic: Diagnostic = rule.fold(error.toDiagnostic)(r => Diag.rule(r)(error.toDiagnostic))

object Rejection:
  /** The call `a` of `d`, which has no measure, in a rule of the measured `c`. */
  def unmeasuredCall(ctx: MeasureCtx, r: Rule, c: RelSym, a: Formula.Atom, d: RelSym, reads: Option[List[RelSym]] = None): Rejection =
    Rejection(TerminationError.UnmeasuredCall(c, d, a.span, ctx.directive(c), ctx.comp, reads), Some(r))
