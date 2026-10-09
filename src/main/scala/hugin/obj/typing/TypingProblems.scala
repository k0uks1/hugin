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

  /** A constant without arguments (`false`, `no`) used as a formula: it holds if the constant is a fact. */
  case ConstantFormula(name: String, at: Span)

  def code: Code = this match
    case _: UndefinedConstant => Code.W0001
    case _: ConstantFormula => Code.W0008

  def primary: Span = this match
    case UndefinedConstant(_, _, _, s) => s
    case ConstantFormula(_, s) => s

  def message: Msg = this match
    case _: UndefinedConstant => msg"undefined constant expression"
    case ConstantFormula(n, _) => msg"the constant ${Src(n)} is used as a formula"

  override def primaryLabel: Msg = this match
    case UndefinedConstant(op, l, r, _) => msg"${Src(s"${l.show} ${op.show} ${r.show}")} is undefined"
    case ConstantFormula(n, _) => msg"holds if ${Src(n)} is a fact"

  override def notes: List[Msg] = this match
    case _: UndefinedConstant => List(msg"the formula containing it never holds, so this rule instance never fires")
    case ConstantFormula(n, _) =>
      List(
        msg"a constant is a fact once a head or an input file builds it, so the formula does not test a value: it holds as soon as any fact contains ${Src(n)}"
      )

  override def helps: List[Msg] = this match
    case ConstantFormula(n, _) => List(msg"to test a value, match it in an atom of a relation, as in ${Src(s"enabled X $n")}")
    case _ => Nil
