package hugin.core
package elab

import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** The problems of `programOf` (reference: std/quote, "Programs as values"): the libraries it builds on
 *  are not loaded (E0940), its argument is not a functor, a functor application or a module (E0941), or a
 *  rule of the module is outside what `std/semantics` models (E0942), or the module is not stratified
 *  (E0950); and the cycles through the program of a file or a body (E0962, #186 P9f). Terms are given as
 *  shown to users. */
enum ProgramOfProblem extends Problem:
  /** `programOf` in a program that does not load `std/quote` and `std/semantics`. */
  case NoLibrary(at: Span)

  /** `programOf p` where `p` (shown) is not a functor, a functor application or a module. */
  case NotAModule(shown: String, at: Span)

  /** A rule of the module at `rule` that `programOf` cannot reify, for `reason`. */
  case CannotReify(reason: String, rule: Span, at: Span)

  /** The relation `relation` of the module depends on `read` through a negation or an aggregate of the
   *  rule at `rule`, and `read` depends on `relation`: the module has no strata. */
  case NotStratified(relation: String, read: String, rule: Span, at: Span)

  /** An item of a file (or a module body, `body`) elaborated before the scope's program exists uses
   *  `used`: a program-dependent declaration, whose `chain` leads to the form that names the program, or
   *  that form itself (`here`). */
  case ProgramCycle(used: String, chain: List[String], body: Boolean, at: Span)

  def code: Code = this match
    case _: NoLibrary => Code.E0940
    case _: NotAModule => Code.E0941
    case _: CannotReify => Code.E0942
    case _: NotStratified => Code.E0950
    case _: ProgramCycle => Code.E0962

  def primary: Span = this match
    case NoLibrary(s) => s
    case NotAModule(_, s) => s
    case CannotReify(_, _, s) => s
    case NotStratified(_, _, _, s) => s
    case ProgramCycle(_, _, _, s) => s

  def message: Msg = this match
    case _: NoLibrary => msg"`programOf` needs the libraries `std/quote` and `std/semantics`"
    case NotAModule(p, _) => msg"${Src(p)} is not a functor, a functor application or a module"
    case CannotReify(reason, _, _) => msg"cannot reify a rule as a program value: " ++ Msg.text(reason)
    case NotStratified(r, s, _, _) =>
      if r == s then msg"the module is not stratified: ${Src(r)} depends on itself through a negation or an aggregate"
      else
        msg"the module is not stratified: ${Src(r)} reads ${Src(s)} through a negation or an aggregate, and ${Src(s)} depends on ${Src(r)}"
    case ProgramCycle(used, chain, body, _) =>
      if chain.isEmpty then msg"${Src(used)}, the program of this ${scopeOf(body)}, is used by an item of its program"
      else msg"this item uses ${Src(used)}, which states a property of the program of this ${scopeOf(body)}"

  override def primaryLabel: Msg = this match
    case _: NoLibrary => msg"`programOf` is used here"
    case _: NotAModule => msg"expected a module"
    case _: CannotReify | _: NotStratified => msg"in the program of this module"
    case ProgramCycle(_, Nil, _, _) => msg"the program is built from this item"
    case _: ProgramCycle => msg"needed to build the program"

  override def labels: List[(Span, Msg)] = this match
    case CannotReify(_, rule, at) if rule.exists && rule != at => List(rule -> msg"this rule")
    case NotStratified(_, _, rule, at) if rule.exists && rule != at => List(rule -> msg"this rule")
    case _ => Nil

  override def notes: List[Msg] = this match
    case _: NoLibrary => List(msg"`programOf` is a form of the code bridge `std/quote`, and builds a `program` of `std/semantics`")
    case NotAModule(_, _) =>
      List(msg"`programOf` reifies the rules of a module body: of a functor, of a functor applied to arguments, or of a module")
    case CannotReify(_, _, _) =>
      List(
        msg"`std/semantics` models atoms, comparisons, negated atoms and aggregates over integers in bodies, the object level's integer arithmetic, and constructor terms of constants with code outside the module"
      )
    case NotStratified(_, _, _, _) =>
      List(
        msg"a negation or an aggregate reads the facts of an earlier stratum, which are complete when it is read (reference: object/negation); the perfect model of `std/strata` needs these strata"
      )
    case ProgramCycle(used, chain, body, _) =>
      val path = (used :: chain).map(n => s"`$n`")
      val through =
        if chain.isEmpty then Nil
        else List(Msg.text(path.sliding(2).map(p => s"${p(0)} uses ${p(1)}").mkString(", ")))
      through :+ msg"the declarations that use the program of their ${scopeOf(body)} (`programOf here`, `here ⊢ r t̄`) are elaborated after its rules, queries and directives, so these, and the declarations they need, cannot use them"

  override def helps: List[Msg] = this match
    case _: NoLibrary => List(msg"add ${Src("%use \"std/quote\".")} and ${Src("%use \"std/semantics\".")} to the file")
    case _: ProgramCycle => List(msg"keep the property out of the rules, or state it about a module of its own, with `programOf m`")
    case _ => Nil

  private def scopeOf(body: Boolean): Lit = Lit(if body then "module body" else "file")
