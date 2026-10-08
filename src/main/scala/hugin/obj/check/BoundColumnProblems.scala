package hugin.obj
package check

import hugin.obj.DiagArgs.given
import hugin.syntax.Bound
import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** Problems of bound columns (docs/REDESIGN.md §5.2): invalid declarations (E0605) and rules over a
 *  bound relation of their own component that are not type-consistent (E0606, [[TypeConsistency]]). */
enum BoundColumnError extends Problem:
  /** A constructor declares a bound column. */
  case InConstructor(rel: RelSym, bound: Bound)

  /** Column `index` (0-based) of `rel` is bound but not its last column. */
  case NotLast(rel: RelSym, bound: Bound, index: Int)

  /** The bound column of `rel` has the non-integer type `tpe`. */
  case NotInteger(rel: RelSym, bound: Bound, tpe: OType)


  /** E0606: a rule violates type-consistency at `at`; `boundBy` is the atom binding the offending limit
   *  variable, with the kind of its bound column, if one is known. */
  case Inconsistent(at: Span, reason: Inconsistency, boundBy: Option[(Span, Bound)] = None)

  def code: Code = this match
    case _: Inconsistent => Code.E0606
    case _ => Code.E0605

  def primary: Span = this match
    case InConstructor(r, _) => r.span
    case NotLast(r, _, _) => r.span
    case NotInteger(r, _, _) => r.span
    case Inconsistent(s, _, _) => s

  def message: Msg = this match
    case InConstructor(r, k) => msg"$k column in the constructor $r"
    case NotLast(r, k, _) => msg"$k column of $r is not the last column"
    case NotInteger(r, k, _) => msg"$k column of $r is not an integer column"
    case Inconsistent(_, why, _) => msg"type-inconsistent rule: " ++ why.message

  override def primaryLabel: Msg = this match
    case _: InConstructor => msg"constructors have no bound columns"
    case NotLast(r, k, i) => msg"column ${i + 1} of ${r.arity} is a $k column"
    case NotInteger(_, _, t) => msg"has type $t"
    case Inconsistent(_, why, _) => why.label

  override def labels: List[(Span, Msg)] = this match
    case Inconsistent(_, _, Some((s, k))) => List(s -> msg"bound by this $k atom")
    case _ => Nil

  override def notes: List[Msg] = this match
    case _: Inconsistent =>
      List(
        msg"in the recursion of a bound relation, improving a value read from a bound column must improve the head (or keep the body true), so that keeping only the best value per key is exact"
      )
    case _ => Nil

  override def helps: List[Msg] = this match
    case _: InConstructor => List(msg"declare a relation with a bound last column instead, e.g. `best : key -> (v : min int) -> rel.`")
    case _: NotLast => List(msg"move the bound column to the end")
    case NotInteger(_, k, _) => List(msg"use ${Src(s"${k.show} int")}")
    case Inconsistent(_, why, _) => List(why.help)

/** Where a value from a bound column is used although it must not be. */
enum Misuse:
  case InAtomColumn
  case InTest(op: CmpOp)
  case InKeyColumn

  /** In the head of `rel`, which has no bound column. */
  case InPlainHead(rel: RelSym)

  def where: Msg = this match
    case InAtomColumn => msg"in a column of an atom"
    case InTest(op) => msg"in the test $op"
    case InKeyColumn => msg"in a key column of the head"
    case InPlainHead(r) => msg"in the head of $r, which has no bound column"

  def help: Msg = this match
    case InAtomColumn => msg"compare it with `<`, `<=`, `>`, `>=` instead, or read the relation from a later component"
    case InTest(_) => msg"compare with `<`, `<=`, `>` or `>=` (a bound value only improves)"
    case InKeyColumn | InPlainHead(_) =>
      msg"a recursive bound value can only flow into the bound column of a bound relation; read it from a later component to use it as a plain value"

/** A linear form over limit variables that type-consistency constrains. */
enum Place:
  case Comparison(cmp: Formula)
  case HeadColumn(bound: Bound)

  def describe: Msg = this match
    case Comparison(f) => msg"the comparison $f"
    case HeadColumn(k) => msg"the head's $k column"

/** Why a rule is not type-consistent (see [[TypeConsistency]]). */
enum Inconsistency:
  /** A recursive atom over `rel` has the non-variable `term` in its bound column. */
  case NotAVariable(rel: RelSym, bound: Bound, term: Term)

  /** The limit variable occurrence `term` is used where improving it is not monotone. */
  case Misused(term: Term, use: Misuse)
  case Negated, Aggregated, InDisjunction

  /** `term` is not linear in a bound value. */
  case NonLinear(term: Term)

  /** The limit variable `variable` has coefficient 0 in `place`. */
  case CancelsOut(variable: VarName, place: Place)

  /** The limit variable `variable`, from a `bound` column, has the wrong sign in `place`, which needs a
   *  positive coefficient from a `positive` column. */
  case WrongSign(variable: VarName, bound: Bound, place: Place, positive: Bound)

  def message: Msg = this match
    case NotAVariable(r, k, _) => msg"the $k column of $r is not a variable"
    case Misused(t, use) => msg"$t from a bound column is used " ++ use.where
    case Negated => msg"a value from a bound column is negated"
    case Aggregated => msg"a value from a bound column is aggregated"
    case InDisjunction => msg"a value from a bound column is used in a disjunction"
    case NonLinear(t) => msg"$t is not linear in a bound value"
    case CancelsOut(v, p) => msg"$v cancels out in ${p.describe}"
    case WrongSign(v, k, p, _) => msg"$v from a $k column has the wrong sign in ${p.describe}"

  def label: Msg = this match
    case _: NotAVariable => msg"a recursive atom over a bound column must bind its value to a variable"
    case Misused(_, use) => msg"used " ++ use.where
    case Negated | Aggregated | InDisjunction => msg"uses a recursive bound value"
    case _: NonLinear => msg"not linear"
    case _: CancelsOut => msg"coefficient 0"
    case WrongSign(v, _, _, _) => msg"improving $v makes this worse"

  def help: Msg = this match
    case NotAVariable(r, _, t) => msg"bind a variable and compare it, e.g. ${Src(s"${r.name} … D, D <= ${ObjPrinter.term(t)}")}"
    case Misused(_, use) => use.help
    case Negated | Aggregated => msg"read the value outside the recursion"
    case InDisjunction => msg"split the rule into one rule per alternative"
    case _: NonLinear => msg"use only `+`, `-` and multiplication by an integer literal on bound values"
    case _: CancelsOut => msg"remove the variable or give it a non-zero coefficient"
    case WrongSign(_, k, p, positive) =>
      val sign = if k == positive then "positive" else "negative"
      msg"in ${p.describe} a value from a $k column needs a ${Lit(sign)} coefficient"
