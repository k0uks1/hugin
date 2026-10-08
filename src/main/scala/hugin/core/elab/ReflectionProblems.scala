package hugin.core
package elab

import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** The problems of reflection (reference: reflection): object syntax that cannot be quoted, holes in the
 *  wrong places (E0917), reflective data that cannot become object code (E0918), and quotes where no
 *  reflective type is expected (E0919). */
enum ReflectionProblem extends Problem:
  /** The reflective types of the prelude are not in scope (`--no-prelude`). */
  case NoReflectiveTypes(at: Span)

  /** Object syntax of a form that has no reflective representation (`what`: "`as`", "a projection"). */
  case Unsupported(what: String, kind: String, at: Span)

  /** Syntax that is not object syntax of the expected kind (`kind`: "a formula", "a term"). */
  case NotObjectSyntax(kind: String, at: Span)

  /** The content of a quote that is not of the category its kind needs (`found`: "a rule", "2 items"). */
  case QuoteShape(kind: String, found: String, at: Span)

  /** A quote expected of a list kind other than a module or a sequence of rules. */
  case QuoteCategory(kind: String, at: Span)

  /** `$..xs` or `$f[t̄]` outside a quote. */
  case HoleOutsideQuote(at: Span)

  /** A quote where the expected type (`expected`, if known) is not a reflective type. */
  case QuoteWithoutType(expected: Option[String], at: Span)

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
    case _: QuoteWithoutType => Code.E0919
    case _ => Code.E0917

  def primary: Span = this match
    case NoReflectiveTypes(s) => s
    case Unsupported(_, _, s) => s
    case NotObjectSyntax(_, s) => s
    case QuoteShape(_, _, s) => s
    case QuoteCategory(_, s) => s
    case HoleOutsideQuote(s) => s
    case QuoteWithoutType(_, s) => s
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
    case QuoteShape(k, f, _) => Msg.text(s"expected $k in this quote, found $f")
    case QuoteCategory(k, _) => Msg.text(s"a quote cannot denote $k")
    case _: HoleOutsideQuote => msg"a hole outside a quote"
    case _: QuoteWithoutType => msg"a quote where no reflective type is expected"
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
    case _: QuoteShape => msg"in this quote"
    case _: QuoteCategory => msg"quoted here"
    case _: HoleOutsideQuote => msg"only inside `'{ … }`"
    case QuoteWithoutType(Some(t), _) => msg"the expected type is ${Src(t)}"
    case QuoteWithoutType(None, _) => msg"the type of this quote is not known"
    case _: MisplacedSequenceHole => msg"sequence hole"
    case _: SequenceHoleNotLast => msg"more elements follow"
    case _: HigherOrderHoleArgument => msg"expected a variable bound by an enclosing aggregate"
    case _: HoleNotVariable => msg"expected `$$X` or `$$_`"
    case NotClosed(s, _) => msg"the value is ${Src(s)}"
    case _: MalformedData => msg"reflected here"

  override def helps: List[Msg] = this match
    case _: QuoteWithoutType => List(msg"give the type: `('{ p X :- q X } : rule)`, or declare it, as in `r : rule = '{ p X :- q X }.`")
    case _ => Nil

  override def notes: List[Msg] = this match
    case _: NoReflectiveTypes =>
      List(msg"`term`, `formula`, `rule`, `item` and `module` are declared by the prelude, which `--no-prelude` leaves out")
    case _: Unsupported =>
      List(
        msg"reflective data represents variables, literals, applications of object constants, arithmetic, comparisons, `not`, `,`, `;` and aggregates"
      )
    case _: NotObjectSyntax =>
      List(msg"quoted object syntax is an object constant applied to terms, a variable, a literal, a hole `$$x`, or a formula")
    case _: QuoteShape =>
      List(
        msg"a `module` (or `seq rule`) quote holds items with their periods, a `rule` or `item` quote one item, a `formula`, `term`, `sym`, `decl` or `measure` quote one of them without a period"
      )
    case _: QuoteCategory => List(msg"a list of formulas or terms is a meta list of quotes: `['{ p X }, '{ q X }]`")
    case _: HoleOutsideQuote =>
      List(msg"`$$..xs` and `$$f[V]` are holes of quoted syntax; outside a quote, `$$x` is the staging splice")
    case _: QuoteWithoutType =>
      List(msg"the category of a quote's content (a module, a rule, a formula, a term, …) is given by the expected reflective type")
    case _: SequenceHoleNotLast => List(msg"a pattern can only match a sequence by its first elements and the rest")
    case _: HigherOrderHoleArgument =>
      List(
        msg"`$$F[V]` matches a formula that may mention `V`, the variable an enclosing aggregate binds; `F` is then a function of type `term -> formula`"
      )
    case _: NotClosed => List(msg"reflection turns closed data into object code during elaboration")
    case _ => Nil
