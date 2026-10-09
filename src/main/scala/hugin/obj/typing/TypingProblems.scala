package hugin.obj
package typing

import hugin.syntax.Literal
import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** Warnings of object typing (lints). */
enum TypingWarning extends Problem:
  /** The object-level expression `left op right` over literals has no value (`1 / 0`). */
  case UndefinedConstant(op: ArithOp, left: Literal, right: Literal, at: Span)

  def code: Code = this match
    case _: UndefinedConstant => Code.W0001

  def primary: Span = this match
    case UndefinedConstant(_, _, _, s) => s

  def message: Msg = this match
    case _: UndefinedConstant => msg"undefined constant expression"

  override def primaryLabel: Msg = this match
    case UndefinedConstant(op, l, r, _) => msg"${Src(s"${l.show} ${op.show} ${r.show}")} is undefined"

  override def notes: List[Msg] = this match
    case _: UndefinedConstant => List(msg"the formula containing it never holds, so this rule instance never fires")
