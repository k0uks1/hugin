package hugin.core
package elab

import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** The argument of an application in an abstracted goal that does not have the type its function expects
 *  (an ill-typed abstraction, E0927): the application, the argument, its type and the expected one, as
 *  shown, and whether the argument's type mentions the abstracted term. */
final case class IllTypedArgument(application: String, argument: String, found: String, expected: String, mentions: Boolean)

/** The problems of `match` and `rewrite` (reference: meta/match): an abstraction that makes the goal
 *  ill-typed (E0927), a `rewrite` that cannot rewrite (E0928), and the equality library they need
 *  (E0929). A `match` that does not cover its scrutinee's cases is E0911, and an unreachable branch W0006
 *  ([[ClauseProblem]]). Names and terms are given as shown to users. */
/** The directive that loads `std/eq`. */
private val UseEq = "%use \"std/eq\"."

enum MatchProblem extends Problem:
  /** Abstracting `term` (the scrutinee of a `match`, `rewrite` = false, or the left side of a `rewrite`'s
   *  equation) in the goal `goal` gives `motive`, with the new variable `variable`, which is ill-typed at
   *  `argument`. */
  case IllTypedAbstraction(
      rewrite: Boolean,
      term: String,
      goal: String,
      variable: String,
      motive: String,
      argument: IllTypedArgument,
      at: Span
  )

  /** `rewrite h in e` with `h` of type `tpe`, which is not an equation `eq a b`. */
  case NotAnEquation(tpe: String, at: Span)

  /** `rewrite h in e` with `h : eq lhs rhs`, where `lhs` does not occur in the normal form `goal` of the goal. */
  case NoOccurrence(lhs: String, goal: String, at: Span)

  /** `rewrite h in e` where the expected type is not known. */
  case RewriteWithoutGoal(at: Span)

  /** `match H : e` (`rewrite` = false) or `rewrite` in a program that does not load `std/eq`; `fileStart`
   *  is where `%use "std/eq".` would go. */
  case NoEqualityLibrary(rewrite: Boolean, at: Span, fileStart: Span)

  def code: Code = this match
    case _: IllTypedAbstraction => Code.E0927
    case _: NotAnEquation | _: NoOccurrence | _: RewriteWithoutGoal => Code.E0928
    case _: NoEqualityLibrary => Code.E0929

  def primary: Span = this match
    case IllTypedAbstraction(_, _, _, _, _, _, s) => s
    case NotAnEquation(_, s) => s
    case NoOccurrence(_, _, s) => s
    case RewriteWithoutGoal(s) => s
    case NoEqualityLibrary(_, s, _) => s

  def message: Msg = this match
    case IllTypedAbstraction(false, t, _, _, _, _, _) => msg"abstracting ${Src(t)} in the goal makes it ill-typed"
    case IllTypedAbstraction(true, t, _, _, _, _, _) => msg"rewriting ${Src(t)} in the goal makes it ill-typed"
    case NotAnEquation(t, _) => msg"cannot rewrite with a proof of ${Src(t)}"
    case NoOccurrence(l, _, _) => msg"the goal does not contain ${Src(l)}, so there is nothing to rewrite"
    case _: RewriteWithoutGoal => msg"the type that `rewrite` should change is not known here"
    case NoEqualityLibrary(false, _, _) => msg"`match H : e` needs the equality of the library `std/eq`"
    case NoEqualityLibrary(true, _, _) => msg"`rewrite` needs the equality of the library `std/eq`"

  override def primaryLabel: Msg = this match
    case IllTypedAbstraction(false, t, _, _, _, _, _) => msg"${Src(t)} is abstracted here"
    case IllTypedAbstraction(true, _, _, _, _, _, _) => msg"the equation used"
    case _: NotAnEquation => msg"not an equation `eq a b`"
    case _: NoOccurrence => msg"nothing to rewrite"
    case _: RewriteWithoutGoal => msg"no expected type"
    case _: NoEqualityLibrary => msg"needs `eq`, `refl`, `subst` and `sym` of `std/eq`"

  override def notes: List[Msg] = this match
    case IllTypedAbstraction(_, t, goal, y, motive, arg, _) =>
      List(
        msg"the goal is ${Src(goal)}; with ${Src(t)} replaced by ${Src(y)} it becomes ${Src(motive)}",
        msg"in ${Src(arg.application)}, the argument ${Src(arg.argument)} has type ${Src(arg.found)}, but ${Src(arg.expected)} is expected"
      ) ++ (if arg.mentions then
              List(
                msg"the type of ${Src(arg.argument)} mentions ${Src(t)}, which is not replaced there: only the occurrences in the goal are abstracted, not those in the types of the terms in it"
              )
            else Nil)
    case _: NotAnEquation => List(msg"`rewrite h in e` needs `h : eq a b`, an equation of `std/eq`; it rewrites `a` to `b` in the goal")
    case NoOccurrence(_, goal, _) => List(msg"the goal, normalised, is ${Src(goal)}")
    case _: RewriteWithoutGoal =>
      List(msg"`rewrite h in e` changes the expected type of the expression; without one there is nothing to change")
    case NoEqualityLibrary(false, _, _) => List(msg"the branches get an equation `eq e p` of the family `eq` of `std/eq`")
    case NoEqualityLibrary(true, _, _) => List(msg"`rewrite h in e` elaborates to `subst P (sym h) e` with `subst` and `sym` of `std/eq`")

  override def helps: List[Msg] = this match
    case IllTypedAbstraction(false, t, _, _, _, arg, _) =>
      List(
        msg"match in a `where`-local function whose type you write, abstracting ${Src(t)} together with what ${Src(arg.argument)} depends on"
      )
    case IllTypedAbstraction(true, t, _, _, _, arg, _) =>
      List(
        msg"rewrite ${Src(arg.argument)} as well (a `rewrite` for an equation of what it depends on), or prove the goal with a `where`-local function whose type you write"
      )
    case _: NoOccurrence => List(msg"to rewrite from right to left, write `rewrite sym h in e`")
    case _: RewriteWithoutGoal => List(msg"use it where its type is known, or give the type: `(rewrite h in e : A)`")
    case _: NoEqualityLibrary => List(msg"add ${Src(UseEq)} to the file")
    case _ => Nil

  override def suggestions: List[Suggestion] = this match
    case NoEqualityLibrary(_, _, start) if start.exists =>
      List(Suggestion.replace(start, UseEq + "\n", msg"add ${Src(UseEq)}", Applicability.MaybeIncorrect))
    case _ => Nil
