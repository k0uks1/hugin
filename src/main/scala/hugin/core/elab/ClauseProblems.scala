package hugin.core
package elab

import hugin.util.Span
import hugin.util.diagnostics.*

/** Why a constructor pattern of a clause cannot occur in the clause's own context. */
enum ClauseConflict:
  /** Index unification ends in a conflict: `a` (from the constructor's type) against `b` (from the
   *  argument's type). */
  case Index(a: String, b: String)

  /** Index unification determined the argument to be `found`, another constructor's application. */
  case Argument(found: String)

  /** The constructor does not belong to the argument's type `tpe`. */
  case Family(tpe: String)
import scala.language.implicitConversions

/** The problems of meta functions and inductive families: coverage (E0911), termination (E0912),
 *  positivity (E0913), the shape of inductive declarations and clauses (E0914), patterns and local
 *  definitions (E0915), and unreachable clauses (W0006). Names and terms are given as shown to users. */
enum ClauseProblem extends Problem:
  case NotCovering(fn: String, missing: String, at: Span)

  /** `call`: a clause on the cycle of calls that does not decrease, with its call. */
  case NotTerminating(fn: String, at: Span, call: Option[(Span, String)])
  case NonPositive(family: String, argument: Int, argumentType: String, at: Span)
  case PartialFamilyResult(family: String, at: Span)
  case ArgumentTooLarge(argument: String, family: String, universe: String, at: Span)
  case NotDefinableByClauses(fn: String, at: Span, declared: Span, kind: String)

  /** `inBody`: the clauses are in a module body, which does not declare the function. */
  case ClausesWithoutDeclaration(fn: String, at: Span, inBody: Boolean = false)
  case PatternCount(fn: String, expected: Int, at: Span)
  case TooManyPatterns(fn: String, explicit: Int, at: Span)
  case ClauseWithoutName(at: Span)
  case TypedPattern(at: Span)
  case PatternArity(constructor: String, expected: Int, found: Int, at: Span)
  case InvalidPattern(at: Span)
  case LiteralPattern(tpe: String, at: Span)

  /** A name in a pattern that is not a constructor (`what`: "`x` is not a constructor", "unresolved name `x`"). */
  case NotAConstructor(what: String, at: Span)
  case BoundTwice(variable: String, at: Span)
  case CannotMatchArgument(argument: String, at: Span)
  case UndecidableConstructor(constructor: String, equation: String, at: Span)
  case NotInductive(tpe: String, at: Span)
  case LocalWithoutClauses(fn: String, at: Span)
  case InvalidLocal(at: Span)
  case BindingNotName(at: Span)
  case BindingArity(constructor: String, fields: Int, found: Int, at: Span)
  case DependentBinding(at: Span)
  case UnreachableClause(fn: String, at: Span)

  /** A constructor pattern that cannot occur in its clause's own context: the clause matches nothing.
   *  `removal` removes the clause; `absurd` (the clause is the function's only one, and no constructor
   *  can occur at the pattern) is the pattern to replace by `()` and the right-hand side to remove. */
  case ImpossibleClause(constructor: String, why: ClauseConflict, at: Span, removal: Option[Span], absurd: Option[(Span, Span)])

  /** An absurd pattern `()` at a position of type `tpe` where the constructors `possible` can occur. */
  case AbsurdNotEmpty(tpe: String, possible: List[String], at: Span)

  /** An absurd clause with a right-hand side: `rhs` is ` = e`, from the patterns to the expression's end. */
  case AbsurdWithRhs(rhs: Span, at: Span)
  case MisplacedAbsurd(at: Span)

  def code: Code = this match
    case _: NotCovering => Code.E0911
    case _: NotTerminating => Code.E0912
    case _: NonPositive => Code.E0913
    case _: PartialFamilyResult | _: ArgumentTooLarge | _: NotDefinableByClauses => Code.E0914
    case _: UnreachableClause => Code.W0006
    case _ => Code.E0915

  def primary: Span = this match
    case NotCovering(_, _, s) => s
    case NotTerminating(_, s, _) => s
    case NonPositive(_, _, _, s) => s
    case PartialFamilyResult(_, s) => s
    case ArgumentTooLarge(_, _, _, s) => s
    case NotDefinableByClauses(_, s, _, _) => s
    case ClausesWithoutDeclaration(_, s, _) => s
    case PatternCount(_, _, s) => s
    case TooManyPatterns(_, _, s) => s
    case ClauseWithoutName(s) => s
    case TypedPattern(s) => s
    case PatternArity(_, _, _, s) => s
    case InvalidPattern(s) => s
    case LiteralPattern(_, s) => s
    case NotAConstructor(_, s) => s
    case BoundTwice(_, s) => s
    case CannotMatchArgument(_, s) => s
    case UndecidableConstructor(_, _, s) => s
    case NotInductive(_, s) => s
    case LocalWithoutClauses(_, s) => s
    case InvalidLocal(s) => s
    case BindingNotName(s) => s
    case BindingArity(_, _, _, s) => s
    case DependentBinding(s) => s
    case UnreachableClause(_, s) => s
    case ImpossibleClause(_, _, s, _, _) => s
    case AbsurdNotEmpty(_, _, s) => s
    case AbsurdWithRhs(_, s) => s
    case MisplacedAbsurd(s) => s

  def message: Msg = this match
    case NotCovering(f, _, _) => msg"the clauses of ${Src(f)} do not cover all cases"
    case NotTerminating(f, _, _) => msg"cannot show that ${Src(f)} terminates"
    case NonPositive(fam, _, _, _) => msg"${Src(fam)} occurs in a non-positive position"
    case PartialFamilyResult(fam, _) => msg"a constructor of ${Src(fam)} must return it applied to all its arguments"
    case ArgumentTooLarge(x, fam, _, _) => msg"the argument ${Src(x)} is too large for ${Src(fam)}"
    case NotDefinableByClauses(f, _, _, _) => msg"${Src(f)} cannot be defined by clauses"
    case ClausesWithoutDeclaration(f, _, _) => msg"clauses of ${Src(f)} without a declaration"
    case PatternCount(f, _, _) => msg"all clauses of ${Src(f)} must have the same number of patterns"
    case TooManyPatterns(f, _, _) => msg"too many patterns for ${Src(f)}"
    case _: ClauseWithoutName => msg"a clause must start with the name of a function"
    case _: TypedPattern => msg"patterns cannot have type annotations"
    case PatternArity(c, e, f, _) => msg"${Src(c)} expects $e argument(s) in a pattern, found $f"
    case _: InvalidPattern => msg"invalid pattern"
    case _: LiteralPattern => msg"literal patterns are only supported for nat-like types"
    case NotAConstructor(w, _) => Msg.text(s"$w in a pattern")
    case BoundTwice(v, _) => msg"the variable ${Src(v)} is bound twice in this clause"
    case _: CannotMatchArgument => msg"cannot match on this argument"
    case UndecidableConstructor(c, _, _) => msg"cannot decide whether ${Src(c)} applies here"
    case _: NotInductive => msg"cannot match on a value of this type"
    case LocalWithoutClauses(f, _) => msg"the local function ${Src(f)} has no clauses"
    case _: InvalidLocal => msg"invalid local definition"
    case _: BindingNotName => msg"a pattern binding binds names"
    case BindingArity(c, n, _, _) => msg"${Src(c)} has $n explicit argument(s)"
    case _: DependentBinding => msg"pattern bindings of dependent fields are not supported"
    case UnreachableClause(f, _) => msg"unreachable clause of ${Src(f)}"
    case ImpossibleClause(c, _, _, _, _) => msg"the case for ${Src(c)} is impossible here"
    case AbsurdNotEmpty(t, _, _) => msg"the type ${Src(t)} is not empty here"
    case _: AbsurdWithRhs => msg"an absurd clause has no right-hand side"
    case _: MisplacedAbsurd => msg"an absurd pattern is only allowed in a clause's patterns"

  override def primaryLabel: Msg = this match
    case NotCovering(_, m, _) => msg"missing: ${Src(m)}"
    case _: NotTerminating => msg"possibly non-terminating"
    case NonPositive(_, k, _, _) => msg"in the type of the constructor's argument $k"
    case _: PartialFamilyResult => msg"partially applied family"
    case _: ArgumentTooLarge => msg"argument in a larger universe"
    case _: NotDefinableByClauses | _: ClausesWithoutDeclaration => msg"clause"
    case PatternCount(_, n, _) => msg"expected $n pattern(s)"
    case TooManyPatterns(f, n, _) => msg"${Src(f)} has $n explicit argument(s)"
    case _: ClauseWithoutName => msg"expected a name"
    case _: TypedPattern => msg"type annotation"
    case _: PatternArity => msg"wrong number of arguments"
    case _: InvalidPattern => msg"not a pattern"
    case LiteralPattern(t, _) => msg"a pattern of type ${Src(t)}"
    case _: NotAConstructor => msg"expected a constructor"
    case _: BoundTwice => msg"bound again here"
    case _: CannotMatchArgument | _: NotInductive => msg"constructor pattern"
    case _: UndecidableConstructor => msg"in this pattern"
    case _: LocalWithoutClauses => msg"declared here"
    case _: InvalidLocal => msg"not allowed in a `where` block"
    case _: BindingNotName => msg"expected a name or `_`"
    case BindingArity(_, _, f, _) => msg"found $f"
    case _: DependentBinding => msg"dependent field"
    case _: UnreachableClause => msg"this clause is never used"
    case ImpossibleClause(_, ClauseConflict.Index(a, b), _, _, _) => msg"its index ${Src(a)} conflicts with ${Src(b)}"
    case ImpossibleClause(_, ClauseConflict.Argument(found), _, _, _) => msg"the argument is ${Src(found)} here"
    case ImpossibleClause(_, ClauseConflict.Family(t), _, _, _) => msg"not a constructor of ${Src(t)}"
    case AbsurdNotEmpty(_, ps, _) => Msg.text(s"${ps.map(c => s"`$c`").mkString(", ")} can occur here")
    case _: AbsurdWithRhs => msg"remove the right-hand side"
    case _: MisplacedAbsurd => msg"absurd pattern"

  override def labels: List[(Span, Msg)] = this match
    case NotTerminating(_, _, Some((sp, shown))) => List(sp -> msg"in this clause: ${Src(shown)}")
    case NotDefinableByClauses(f, _, d, k) => List(d -> msg"${Src(f)} is declared here as ${Lit(k)}")
    case _ => Nil

  override def notes: List[Msg] = this match
    case _: NotCovering => List(msg"meta functions are total: every argument must match a clause")
    case _: NotTerminating =>
      List(
        msg"meta functions must be total: some argument must get structurally smaller (a constructor subterm of a pattern) along every cycle of calls"
      )
    case NonPositive(_, _, t, _) =>
      List(
        msg"the argument has type ${Src(t)}",
        msg"a family may only occur strictly positively in the arguments of its constructors: not to the left of an arrow, nor inside the arguments of another type"
      )
    case ArgumentTooLarge(_, fam, u, _) =>
      List(msg"${Src(fam)} lives in ${Src(u)}; its constructors may only take arguments of types in that universe (predicativity)")
    case _: NotDefinableByClauses => List(msg"clauses define meta functions; object relations are defined by rules (`:-`)")
    case _: InvalidPattern => List(msg"patterns are uppercase variables, `_`, constructors applied to patterns and natural-number literals")
    case _: NotAConstructor => List(msg"pattern variables are uppercase; lowercase names in patterns are constructors")
    case CannotMatchArgument(a, _) => List(msg"the argument is ${Src(a)}, which is neither a variable nor a constructor application")
    case UndecidableConstructor(_, eq, _) =>
      List(msg"unifying the indices of its type requires ${Src(eq)}, which is neither solvable nor impossible")
    case NotInductive(t, _) => List(msg"the argument has type ${Src(t)}, which is not an inductive type")
    case _: InvalidLocal =>
      List(
        msg"a `where` block contains definitions `x = e.`, local functions (`f : A.` and clauses `f p̄ = e.`) and pattern bindings `c x̄ = e.`"
      )
    case _: UnreachableClause => List(msg"the clauses before it cover all the cases it matches")
    case _: ImpossibleClause =>
      List(msg"a clause is checked in its own context: no argument can match its patterns, so the clause can never apply")
    case _: AbsurdNotEmpty => List(msg"an absurd pattern `()` stands for a position none of whose constructors can occur")
    case _: AbsurdWithRhs => List(msg"a clause with an absurd pattern `()` matches no argument, so it has no right-hand side")
    case _: MisplacedAbsurd => List(msg"`()` marks a pattern position of an empty type in an absurd clause `f p̄.`")
    case ClausesWithoutDeclaration(_, _, true) => List(msg"the clauses of a module body define the functions that the body declares")
    case _ => Nil

  override def suggestions: List[Suggestion] = this match
    case ImpossibleClause(_, _, _, removal, absurd) =>
      removal.toList.map(r => Suggestion.replace(r, "", msg"remove the clause", Applicability.MachineApplicable)) ++
        absurd.toList.map { (pat, rhs) =>
          Suggestion(
            "replace the pattern by the absurd pattern `()` and remove the right-hand side",
            List(Edit(pat, "()"), Edit(rhs, "")),
            Applicability.MachineApplicable
          )
        }
    case AbsurdWithRhs(rhs, _) => List(Suggestion.replace(rhs, "", msg"remove the right-hand side", Applicability.MachineApplicable))
    case _ => Nil

  override def helps: List[Msg] = this match
    case NotCovering(_, m, _) => List(msg"add a clause ${Src(s"$m = ….")}")
    case ClausesWithoutDeclaration(f, _, inBody) =>
      List(msg"declare its type first${Lit(if inBody then " in the body" else "")}: ${Src(s"$f : A -> B.")}")
    case _ => Nil
