package hugin.util.diagnostics

import hugin.util.Span
import scala.language.implicitConversions

/** Warnings that users may want to silence: each has a lint name in its [[Code]] (`Code.lint`). The
 *  other lints (W0002, W0003, W0005) are still reported by the old meta typer through `Legacy`. */
enum Lint extends Problem:
  /** An object-level expression over literals whose value is undefined, as written (`1 / 0`). */
  case UndefinedConstant(expr: String, at: Span)

  def code: Code = this match
    case _: UndefinedConstant => Code.W0001

  def primary: Span = this match
    case UndefinedConstant(_, s) => s

  def message: Msg = this match
    case _: UndefinedConstant => msg"undefined constant expression"

  override def primaryLabel: Msg = this match
    case UndefinedConstant(e, _) => msg"${Src(e)} is undefined"

  override def notes: List[Msg] = this match
    case _: UndefinedConstant => List(msg"the formula containing it never holds, so this rule instance never fires")
