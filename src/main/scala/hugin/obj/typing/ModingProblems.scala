package hugin.obj
package typing

import hugin.obj.DiagArgs.given
import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** The kind of formula whose variables are not bound, which determines how to bind them. */
enum UnboundSite:
  case Equation, Comparison, Aggregate, Negation, Other

/** Problems of range restriction and moding (E0501–E0503). `checking` is the mode of the rule's head
 *  relation that was being checked, if that relation has declared modes. */
enum ModingError extends Problem:
  /** A call of a moded relation none of whose `modes` applies; `unboundArgs` are the inputs (0-based) of
   *  the closest mode that are not bound, `unbound` their variables. */
  case NoApplicableMode(
      rel: RelSym,
      at: Span,
      modes: List[Mode],
      unboundArgs: List[Int],
      unbound: List[VarName],
      checking: Option[(Mode, RelSym)] = None
  )
  case UnboundInFormula(missing: List[VarName], site: UnboundSite, at: Span, checking: Option[(Mode, RelSym)] = None)
  case NotRangeRestricted(missing: List[VarName], at: Span, others: List[Span], checking: Option[(Mode, RelSym)])
  case HeadInputNotPattern(rel: RelSym, index: Int, mode: Mode, at: Span)

  def code: Code = this match
    case _: NoApplicableMode => Code.E0502
    case _: HeadInputNotPattern => Code.E0503
    case _ => Code.E0501

  def primary: Span = this match
    case NoApplicableMode(_, s, _, _, _, _) => s
    case UnboundInFormula(_, _, s, _) => s
    case NotRangeRestricted(_, s, _, _) => s
    case HeadInputNotPattern(_, _, _, s) => s

  def message: Msg = this match
    case NoApplicableMode(c, _, _, _, _, _) => msg"call to $c without an applicable mode"
    case UnboundInFormula(vs, _, _, _) => msg"unbound variable${plural(vs)} ${names(vs)}"
    case _: NotRangeRestricted => msg"rule is not range-restricted"
    case HeadInputNotPattern(c, i, _, _) => msg"input position ${i + 1} of $c is not a pattern"

  override def primaryLabel: Msg = this match
    case NoApplicableMode(_, _, _, args, _, _) => Msg.join(args.map(i => msg"argument ${i + 1} is not bound"), ", ")
    case _: UnboundInFormula => msg"cannot be evaluated: not all variables are bound"
    case NotRangeRestricted(vs, _, _, _) => msg"${names(vs)} not bound by the body"
    case _: HeadInputNotPattern => msg"arithmetic, projections and updates are not allowed here"

  override def labels: List[(Span, Msg)] = this match
    case NotRangeRestricted(_, _, others, _) => others.map(_ -> Msg.empty)
    case _ => Nil

  override def notes: List[Msg] = this match
    case NoApplicableMode(c, _, modes, _, unbound, checking) =>
      val declared = msg"declared mode${Lit(if modes.length > 1 then "s" else "")} of $c: ${Lit(modes.map(_.show).mkString(", "))}"
      val vars = if unbound.isEmpty then Nil else List(msg"unbound variable${plural(unbound)}: ${names(unbound)}")
      declared :: vars ++ checkingNote(checking)
    case UnboundInFormula(_, site, _, checking) => siteNote(site) :: checkingNote(checking)
    case NotRangeRestricted(_, _, _, checking) =>
      msg"every variable of the head must be bound by a positive atom or an equation in the body" :: checkingNote(checking)
    case HeadInputNotPattern(c, _, m, _) => List(msg"$c has mode ${Lit(m.show)}; its inputs must appear in the demand guard")

  override def helps: List[Msg] = this match
    case _: NoApplicableMode => List(msg"bind the input arguments with earlier formulas in the body")
    case _ => Nil

  /** The problem while checking `mode` of the head relation `rel` (noted if `rel` has declared modes). */
  def checking(mode: Mode, rel: RelSym): ModingError = this match
    case p: NoApplicableMode => p.copy(checking = Some((mode, rel)))
    case p: UnboundInFormula => p.copy(checking = Some((mode, rel)))
    case p: NotRangeRestricted => p.copy(checking = Some((mode, rel)))
    case p: HeadInputNotPattern => p

  private def checkingNote(c: Option[(Mode, RelSym)]): List[Msg] =
    c.toList.map((m, r) => msg"while checking mode ${Lit(m.show)} of $r")

  private def siteNote(site: UnboundSite): Msg = site match
    case UnboundSite.Equation => msg"an equation binds a variable or pattern on one side only when the other side is fully bound"
    case UnboundSite.Comparison => msg"comparisons require both sides to be bound"
    case UnboundSite.Aggregate => msg"the aggregated term must be bound by the aggregate's body"
    case UnboundSite.Negation => msg"arithmetic and projections under `not` must be bound before the negation"
    case UnboundSite.Other => msg"variables must be bound by a relation atom or an equation"

  private def plural(vs: List[VarName]): Lit = Lit(if vs.size > 1 then "s" else "")
  private def names(vs: List[VarName]): Msg = Msg.join(vs.map(v => msg"$v"), ", ")
