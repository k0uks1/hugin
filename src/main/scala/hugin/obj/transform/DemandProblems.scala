package hugin.obj
package transform

import hugin.obj.DiagArgs.given
import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** Problems of the built-in demand transformation (E0504). It goes with the transformation (docs/REDESIGN.md
 *  §10, C3). Relations are shown by their display names (instances as their polymorphic relation). */
enum DemandError extends Problem:
  /** The input `term` of a call of `rel` with mode `mode` (declared at `modeAt`) builds a fact of the fact
   *  constructor `ctor`: the demand rule would add it to the database. */
  case FactInModedInput(rel: RelSym, mode: Mode, modeAt: Option[Span], term: Term, ctor: RelSym)

  def code: Code = this match
    case _: FactInModedInput => Code.E0504

  def primary: Span = this match
    case p: FactInModedInput => p.term.span

  def message: Msg = this match
    case _: FactInModedInput => msg"fact constructor built in a moded input"

  override def primaryLabel: Msg = this match
    case FactInModedInput(c, _, _, t, _) => msg"$t would be built as an input of ${name(c)}"

  override def labels: List[(Span, Msg)] = this match
    case FactInModedInput(c, m, at, _, _) => at.filter(_.exists).toList.map(_ -> msg"the call uses mode $m of ${name(c)}")

  override def notes: List[Msg] = this match
    case FactInModedInput(_, _, _, t, f) =>
      List(
        msg"${name(f)} is a fact constructor (`%fact`): building $t makes it a fact of ${name(f)}, and a moded call builds its inputs as demands, so `%mode` would change the database"
      )

  override def helps: List[Msg] = this match
    case FactInModedInput(_, _, _, t, f) =>
      List(
        msg"if ${name(f)} is only used as a value, remove `%fact` from its declaration",
        msg"otherwise bind an existing fact first and pass the variable, e.g. ${Src(s"S = ${ObjPrinter.term(t)}")} before the call"
      )

  private def name(r: RelSym): Src = Src(r.displayName)
