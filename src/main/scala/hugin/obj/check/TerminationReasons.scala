package hugin.obj
package check

import hugin.obj.DiagArgs.given
import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** Why a rule invents values, i.e. why it is constructive (Definition 10.1, refined; see
 *  [[Constructive.constructive]]): the construct at [[at]] can take infinitely many values. */
enum Invention:
  /** The head builds a constructor term that the body does not match. */
  case HeadConstructs(term: Term)

  /** A head variable is bound to a new data term by a binding equation. */
  case BuiltByEquation(variable: VarName, equation: Formula)

  /** A fact matched with `as` is put into the head (at the whole rule). */
  case LiftedFact(variable: VarName, rule: Span)

  /** The head computes an arithmetic term. */
  case HeadComputes(term: Term)

  /** A head variable is computed by an arithmetic equation. */
  case ComputedByEquation(variable: VarName, equation: Formula)

  /** The smallest span that shows the invention. */
  def at: Span = this match
    case HeadConstructs(t) => t.span
    case BuiltByEquation(_, e) => e.span
    case LiftedFact(_, s) => s
    case HeadComputes(t) => t.span
    case ComputedByEquation(_, e) => e.span

  def describe: Msg = this match
    case HeadConstructs(t) => msg"its head constructs $t, which is not matched in the body"
    case BuiltByEquation(v, e) => msg"head variable $v is built by $e"
    case LiftedFact(v, _) => msg"the matched fact $v is lifted into the head"
    case HeadComputes(t) => msg"its head computes $t"
    case ComputedByEquation(v, e) => msg"head variable $v is computed by $e"

/** Why direction (A), descent along derivations ([[SizeChange]]), fails. */
enum DescentFailure:
  /** A cycle of derivation steps from `from` back to `to`, through the rules at `rules`, whose composed
   *  size-change graph is idempotent and has no strict self-arc. */
  case NoDescent(from: RelSym, to: RelSym, rules: List[Span])

  /** The composition closure exceeded its bound, so the criterion was not decided. */
  case TooManyGraphs

  def note: Msg = this match
    case NoDescent(from, to, rules) =>
      val via = rules.map(s => s"rule at ${s.show}").distinct.mkString(", ")
      msg"descent along derivations (A) fails: along $from -> ... -> $to (${Lit(via)}) no argument of the derived fact is smaller than in the premise"
    case TooManyGraphs => msg"descent along derivations (A) fails: the size-change graphs of the component are too many to check"

object DescentFailure:
  def of(f: SizeChange.Failure): DescentFailure = f.chain match
    case Some(c) => NoDescent(c.from, c.to, c.steps.map(_.rule.span))
    case None => TooManyGraphs

/** The measure of one relation in guarded induction (B): the argument `positions`, compared
 *  lexicographically; `slots` says which components are integers (the others are compared by the
 *  proper-subterm relation). All measures compared with each other have the same `slots`. */
final case class Measure(rel: RelSym, positions: List[Int], slots: List[Boolean]):
  def lexicographic: Boolean = slots.length > 1

  /** "component 2 of the measure: " in front of a slot's explanation, for a lexicographic measure. */
  def component(i: Int): Msg = if lexicographic then msg"component ${i + 1} of the measure: " else Msg.empty

  /** "argument 1 `n` (integer), argument 2 (structural)". */
  def positionsShown: Msg = Msg.text(Termination.showPositions(rel, positions))

/** Which two places a measure is compared between: it must be smaller at `small` than at `big`. */
enum Roles(val small: String, val big: String):
  /** Bottom-up: a recursive call against the head of its rule. */
  case CallAndHead extends Roles("the call", "the head")

  /** Demand-driven: the demand of a call against the demand of its caller. */
  case CallAndCaller extends Roles("the call", "the caller")

/** A bound in a direction that a guard would add to make a step of [[SizeChange]] strict: the integer
 *  argument `head` of the conclusion is smaller (or, with `up`, larger) than `premise`. */
final case class MissingGuard(head: Term, premise: Term, up: Boolean):
  def help: Msg =
    val (hs, ss) = (ObjPrinter.term(head), ObjPrinter.term(premise))
    val guard = if up then s"$hs < 100" else s"$hs >= 0"
    val (cmp, dir) = if up then ("larger", "above") else ("smaller", "below")
    msg"$head is ${Lit(cmp)} than $premise but not bounded ${Lit(dir)}: add a guard such as ${Src(guard)} (or bound $premise)"

object MissingGuard:
  def of(h: SizeChange.Hint): MissingGuard = MissingGuard(h.head, h.premise, h.up)
