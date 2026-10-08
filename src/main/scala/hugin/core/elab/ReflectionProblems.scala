package hugin.core
package elab

import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** The problems of reflection (reference: reflection): object syntax that cannot be quoted, holes in the
 *  wrong places (E0917), and reflective data that cannot become object code (E0918). */
enum ReflectionProblem extends Problem:
  /** The reflective types of the prelude are not in scope (`--no-prelude`). */
  case NoReflectiveTypes(at: Span)

  /** Object syntax of a form that has no reflective representation (`what`: "`as`", "a projection"). */
  case Unsupported(what: String, kind: String, at: Span)

  /** Syntax that is not object syntax of the expected kind (`kind`: "a formula", "a term"). */
  case NotObjectSyntax(kind: String, at: Span)

  /** `$..xs` where a single element is expected. */
  case MisplacedSequenceHole(at: Span)

  /** `$..xs` in a pattern, before the end of its sequence. */
  case SequenceHoleNotLast(at: Span)

  /** `$f[t̄]` in a pattern whose arguments are not variables bound by enclosing aggregates. */
  case HigherOrderHoleArgument(at: Span)

  /** A hole in a pattern that does not bind a variable (`$(f X)`). */
  case HoleNotVariable(at: Span)

  /** Reflective data that is not closed (it depends on a variable or a stuck computation). */
  case NotClosed(shown: String, at: Span)

  /** Reflective data that does not describe object code (`what`: why). */
  case MalformedData(what: String, at: Span)

  def code: Code = this match
    case _: NotClosed | _: MalformedData => Code.E0918
    case _ => Code.E0917

  def primary: Span = this match
    case NoReflectiveTypes(s) => s
    case Unsupported(_, _, s) => s
    case NotObjectSyntax(_, s) => s
    case MisplacedSequenceHole(s) => s
    case SequenceHoleNotLast(s) => s
    case HigherOrderHoleArgument(s) => s
    case HoleNotVariable(s) => s
    case NotClosed(_, s) => s
    case MalformedData(_, s) => s

  def message: Msg = this match
    case _: NoReflectiveTypes => msg"the reflective types of the prelude are not in scope"
    case Unsupported(w, k, _) => Msg.text(s"$w cannot be quoted as $k")
    case NotObjectSyntax(k, _) => Msg.text(s"expected object syntax of $k")
    case _: MisplacedSequenceHole => msg"a sequence hole `$$..` where a single element is expected"
    case _: SequenceHoleNotLast => msg"a sequence hole `$$..` must end its sequence in a pattern"
    case _: HigherOrderHoleArgument => msg"the arguments of a higher-order hole must be variables bound by an aggregate"
    case _: HoleNotVariable => msg"a hole in a pattern must be a variable or `_`"
    case _: NotClosed => msg"cannot reflect a value that is not known at compile time"
    case MalformedData(w, _) => Msg.text(s"cannot reflect this value: $w")

  override def primaryLabel: Msg = this match
    case _: NoReflectiveTypes => msg"object syntax as data"
    case _: Unsupported => msg"not supported in quoted syntax"
    case _: NotObjectSyntax => msg"not object syntax"
    case _: MisplacedSequenceHole => msg"sequence hole"
    case _: SequenceHoleNotLast => msg"more elements follow"
    case _: HigherOrderHoleArgument => msg"expected a variable bound by an enclosing aggregate"
    case _: HoleNotVariable => msg"expected `$$X` or `$$_`"
    case NotClosed(s, _) => msg"the value is ${Src(s)}"
    case _: MalformedData => msg"reflected here"

  override def notes: List[Msg] = this match
    case _: NoReflectiveTypes =>
      List(msg"`term`, `formula`, `rule`, `item` and `module` are declared by the prelude, which `--no-prelude` leaves out")
    case _: Unsupported =>
      List(
        msg"reflective data represents variables, literals, applications of object constants, arithmetic, comparisons, `not`, `,`, `;` and aggregates"
      )
    case _: NotObjectSyntax =>
      List(
        msg"in a position of a reflective type, object syntax is quoted: an object constant applied to terms, a hole `$$x`, or a formula"
      )
    case _: SequenceHoleNotLast => List(msg"a pattern can only match a sequence by its first elements and the rest")
    case _: HigherOrderHoleArgument =>
      List(
        msg"`$$F[V]` matches a formula that may mention `V`, the variable an enclosing aggregate binds; `F` is then a function of type `term -> formula`"
      )
    case _: NotClosed => List(msg"reflection turns closed data into object code during elaboration")
    case _ => Nil
