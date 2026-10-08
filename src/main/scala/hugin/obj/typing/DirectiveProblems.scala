package hugin.obj
package typing

import hugin.obj.DiagArgs.given
import hugin.util.{Origin, Span}
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** Problems of directives attached to relations (E0701). Every case lies in the directive at `at`, whose
 *  meta-level expansion chain is `from`. */
enum DirectiveError extends Problem:
  case ModeArity(rel: RelSym, items: Int, at: Span, from: Origin)

  /** A mode item `+l` whose label `label` is not that of column `column` (0-based). */
  case ModeLabel(rel: RelSym, label: String, column: Int, at: Span, from: Origin)
  case TerminatesArity(rel: RelSym, args: Int, at: Span, from: Origin)
  case MeasureVariableTwice(v: String, at: Span, from: Origin)
  case MeasureVariableNotOnce(v: String, at: Span, from: Origin)
  case MeasureUnknownLabel(rel: RelSym, label: String, at: Span, from: Origin)
  case MeasureLabelTwice(label: String, at: Span, from: Origin)
  case UnknownRule(name: String, at: Span, from: Origin)

  def code: Code = Code.E0701

  def primary: Span = this match
    case ModeArity(_, _, s, _) => s
    case ModeLabel(_, _, _, s, _) => s
    case TerminatesArity(_, _, s, _) => s
    case MeasureVariableTwice(_, s, _) => s
    case MeasureVariableNotOnce(_, s, _) => s
    case MeasureUnknownLabel(_, _, s, _) => s
    case MeasureLabelTwice(_, s, _) => s
    case UnknownRule(_, s, _) => s

  def message: Msg = this match
    case ModeArity(r, n, _, _) => msg"mode for $r has $n items but the relation has ${r.arity} columns"
    case ModeLabel(r, l, i, _, _) =>
      val col = r.cols(i).label.fold(msg"unlabelled")(x => msg"labelled ${Src(x)}")
      msg"mode item names label ${Src(l)}, but column ${i + 1} of $r is $col"
    case TerminatesArity(r, n, _, _) => msg"`%terminates` pattern has $n arguments but $r has ${r.arity} columns"
    case MeasureVariableTwice(v, _, _) => msg"variable ${Src(v)} occurs twice in the measure"
    case MeasureVariableNotOnce(v, _, _) => msg"variable ${Src(v)} must occur exactly once in the pattern"
    case MeasureUnknownLabel(r, l, _, _) => msg"$r has no column labelled ${Src(l)}"
    case MeasureLabelTwice(l, _, _) => msg"label ${Src(l)} occurs twice in the measure"
    case UnknownRule(n, _, _) => msg"no rule named ${Src("@" + n)}"

  override def primaryLabel: Msg = this match
    case _: MeasureVariableTwice | _: MeasureVariableNotOnce | _: MeasureLabelTwice => msg"ambiguous position"
    case _: UnknownRule => msg"unknown rule"
    case _ => Msg.empty

  override def origin: Origin = this match
    case ModeArity(_, _, _, o) => o
    case ModeLabel(_, _, _, _, o) => o
    case TerminatesArity(_, _, _, o) => o
    case MeasureVariableTwice(_, _, o) => o
    case MeasureVariableNotOnce(_, _, o) => o
    case MeasureUnknownLabel(_, _, _, o) => o
    case MeasureLabelTwice(_, _, o) => o
    case UnknownRule(_, _, o) => o

/** Where to insert a directive as a line of its own: before the declaration at `at`, indented by `indent`. */
final case class DirectiveInsertion(at: Span, indent: String)

/** A relation passed to a functor does not satisfy a requirement of the parameter's signature (E0208).
 *  `use` is the argument, `required` the requirement in the signature, `from` the functor application. */
enum RequirementError extends Problem:
  case NotComplete(rel: RelSym, label: String, use: Span, required: Span, from: Origin)
  case MissingMode(rel: RelSym, label: String, mode: Mode, use: Span, required: Span, from: Origin, insert: Option[DirectiveInsertion])

  def code: Code = Code.E0208

  def primary: Span = this match
    case NotComplete(_, _, s, _, _) => s
    case MissingMode(_, _, _, s, _, _, _) => s

  def message: Msg = this match
    case NotComplete(r, l, _, _, _) => msg"relation $r does not satisfy ${Src(s"%complete $l")}"
    case MissingMode(r, _, m, _, _, _, _) => msg"relation $r does not have mode $m"

  override def primaryLabel: Msg = this match
    case NotComplete(r, _, _, _, _) => msg"$r is open"
    case MissingMode(_, l, _, _, _, _, _) => msg"required for field ${Src(l)}"

  override def labels: List[(Span, Msg)] = this match
    case NotComplete(_, _, _, req, _) => List(req -> msg"required here")
    case MissingMode(_, _, _, _, req, _, _) => List(req -> msg"required here")

  override def notes: List[Msg] = this match
    case _: NotComplete => List(msg"the functor negates or aggregates over this relation, which needs complete knowledge")
    case _ => Nil

  override def helps: List[Msg] = this match
    case MissingMode(r, _, m, _, _, _, _) => List(msg"declare ${Src(directive(r, m))}")
    case _ => Nil

  override def suggestions: List[Suggestion] = this match
    case MissingMode(r, _, m, _, _, _, Some(DirectiveInsertion(at, indent))) =>
      val d = directive(r, m)
      List(Suggestion.replace(at, s"$d\n$indent", msg"declare ${Src(d)}", Applicability.MachineApplicable))
    case _ => Nil

  override def origin: Origin = this match
    case NotComplete(_, _, _, _, o) => o
    case MissingMode(_, _, _, _, _, o, _) => o

  private def directive(r: RelSym, m: Mode): String = s"%mode ${r.name} ${m.inputs.map(b => if b then "+" else "-").mkString(" ")}."
