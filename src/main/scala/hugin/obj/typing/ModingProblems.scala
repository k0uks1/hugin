package hugin.obj
package typing

import hugin.obj.DiagArgs.given
import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** The kind of formula whose variables are not bound, which determines how to bind them. */
enum UnboundSite:
  case Equation, Comparison, Aggregate, Negation, Other

/** Problems of range restriction (E0501). */
enum ModingError extends Problem:
  case UnboundInFormula(missing: List[VarName], site: UnboundSite, at: Span)
  case NotRangeRestricted(missing: List[VarName], at: Span, others: List[Span])

  def code: Code = Code.E0501

  def primary: Span = this match
    case UnboundInFormula(_, _, s) => s
    case NotRangeRestricted(_, s, _) => s

  def message: Msg = this match
    case UnboundInFormula(vs, _, _) => msg"unbound variable${plural(vs)} ${names(vs)}"
    case _: NotRangeRestricted => msg"rule is not range-restricted"

  override def primaryLabel: Msg = this match
    case _: UnboundInFormula => msg"cannot be evaluated: not all variables are bound"
    case NotRangeRestricted(vs, _, _) => msg"${names(vs)} not bound by the body"

  override def labels: List[(Span, Msg)] = this match
    case NotRangeRestricted(_, _, others) => others.map(_ -> Msg.empty)
    case _ => Nil

  override def notes: List[Msg] = this match
    case UnboundInFormula(_, site, _) => List(siteNote(site))
    case _: NotRangeRestricted => List(msg"every variable of the head must be bound by a positive atom or an equation in the body")

  private def siteNote(site: UnboundSite): Msg = site match
    case UnboundSite.Equation => msg"an equation binds a variable or pattern on one side only when the other side is fully bound"
    case UnboundSite.Comparison => msg"comparisons require both sides to be bound"
    case UnboundSite.Aggregate => msg"the aggregated term must be bound by the aggregate's body"
    case UnboundSite.Negation => msg"arithmetic and projections under `not` must be bound before the negation"
    case UnboundSite.Other => msg"variables must be bound by a relation atom or an equation"

  private def plural(vs: List[VarName]): Lit = Lit(if vs.size > 1 then "s" else "")
  private def names(vs: List[VarName]): Msg = Msg.join(vs.map(v => msg"$v"), ", ")
