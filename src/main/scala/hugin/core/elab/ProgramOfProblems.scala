package hugin.core
package elab

import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** The problems of `programOf` (reference: std/quote, "Programs as values"): the libraries it builds on
 *  are not loaded (E0940), its argument is not a functor, a functor application or a module (E0941), or a
 *  rule of the module is outside what `std/semantics` models (E0942). Terms are given as shown to users. */
enum ProgramOfProblem extends Problem:
  /** `programOf` in a program that does not load `std/quote`. */
  case NoLibrary(at: Span)

  /** `programOf p` where `p` (shown) is not a functor, a functor application or a module; `here` if it is
   *  the name `here`. */
  case NotAModule(shown: String, here: Boolean, at: Span)

  /** A rule of the module at `rule` that `programOf` cannot reify, for `reason`. */
  case CannotReify(reason: String, rule: Span, at: Span)

  def code: Code = this match
    case _: NoLibrary => Code.E0940
    case _: NotAModule => Code.E0941
    case _: CannotReify => Code.E0942

  def primary: Span = this match
    case NoLibrary(s) => s
    case NotAModule(_, _, s) => s
    case CannotReify(_, _, s) => s

  def message: Msg = this match
    case _: NoLibrary => msg"`programOf` needs the code bridge `std/quote`"
    case NotAModule(p, _, _) => msg"${Src(p)} is not a functor, a functor application or a module"
    case CannotReify(reason, _, _) => msg"cannot reify a rule as a program value: " ++ Msg.text(reason)

  override def primaryLabel: Msg = this match
    case _: NoLibrary => msg"`programOf` is used here"
    case _: NotAModule => msg"expected a module"
    case _: CannotReify => msg"in the program of this module"

  override def labels: List[(Span, Msg)] = this match
    case CannotReify(_, rule, at) if rule.exists && rule != at => List(rule -> msg"this rule")
    case _ => Nil

  override def notes: List[Msg] = this match
    case _: NoLibrary => List(msg"`programOf` builds a `program` of `std/semantics` with the vocabulary of `std/quote`")
    case NotAModule(_, true, _) =>
      List(
        msg"`programOf here`, the program of the current file, is not available yet: it needs the file's rules before its meta definitions"
      )
    case NotAModule(_, false, _) =>
      List(msg"`programOf` reifies the rules of a module body: of a functor, of a functor applied to arguments, or of a module")
    case CannotReify(_, _, _) =>
      List(
        msg"`std/semantics` models atoms and comparisons in bodies, the object level's integer arithmetic, and constructor terms of constants with code outside the module"
      )

  override def helps: List[Msg] = this match
    case _: NoLibrary => List(msg"add ${Src("%use \"std/quote\".")} to the file")
    case _ => Nil
