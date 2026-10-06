package hugin.obj

import hugin.util.*
import hugin.syntax.{AggKind, Literal}
import hugin.meta.MExpr

enum ArithOp:
  case Add, Sub, Mul, Div, Concat
  def show: String = this match
    case Add => "+"
    case Sub => "-"
    case Mul => "*"
    case Div => "/"
    case Concat => "^"
object ArithOp:
  def fromString(s: String): Option[ArithOp] = s match
    case "+" => Some(Add)
    case "-" => Some(Sub)
    case "*" => Some(Mul)
    case "/" => Some(Div)
    case "^" => Some(Concat)
    case _ => None

enum CmpOp:
  case Eq, Ne, Lt, Le, Gt, Ge
  def show: String = this match
    case Eq => "="
    case Ne => "<>"
    case Lt => "<"
    case Le => "<="
    case Gt => ">"
    case Ge => ">="
object CmpOp:
  def fromString(s: String): Option[CmpOp] = s match
    case "=" => Some(Eq)
    case "<>" => Some(Ne)
    case "<" => Some(Lt)
    case "<=" => Some(Le)
    case ">" => Some(Gt)
    case ">=" => Some(Ge)
    case _ => None

/** Reference to a relation: resolved, or (before meta evaluation) a spliced meta expression. */
enum RelRef:
  case Sym(rel: RelSym)
  case Spliced(m: MExpr)
  def show: String = this match
    case Sym(r) => r.name
    case Spliced(m) => s"~(${MExpr.show(m)})"
  def sym: RelSym = this match
    case Sym(r) => r
    case Spliced(m) => throw IllegalStateException(s"unevaluated relation splice ${MExpr.show(m)}")

object Var:
  /** Wildcards become fresh variables with this prefix. */
  val WildPrefix = "_#"
  def isWild(n: String): Boolean = n.startsWith(WildPrefix)

  /** User-facing name: wildcards print as `_`, hygiene suffixes `#k` (Section 4.8) are dropped. */
  def display(n: String): String =
    if isWild(n) then "_"
    else
      val base = n.replaceAll("(#\\d+)+$", "")
      if base.isEmpty then n else base

/** Object terms, patterns and head terms (Figure 2). */
sealed trait Term:
  def span: Span

object Term:
  final case class Var(name: String)(val span: Span) extends Term
  final case class Lit(value: Literal)(val span: Span) extends Term

  /** Constructor term / fact pattern `c t̄`. */
  final case class App(rel: RelRef, args: List[Term])(val span: Span) extends Term

  final case class As(t: Term, v: String)(val span: Span) extends Term
  final case class Ascr(t: Term, tpe: OType)(val span: Span) extends Term
  final case class Proj(v: Term, label: String)(val span: Span) extends Term
  final case class With(v: Term, fields: List[(String, Term, Span)])(val span: Span) extends Term
  final case class Arith(op: ArithOp, l: Term, r: Term)(val span: Span) extends Term
  final case class Neg(t: Term)(val span: Span) extends Term

  /** Splice of a meta expression of type ⇑τ or a meta primitive (persisted). */
  final case class Splice(m: MExpr)(val span: Span) extends Term

/** Formulas (Figure 2). Bodies are lists (conjunctions). */
sealed trait Formula:
  def span: Span

object Formula:
  final case class Atom(rel: RelRef, args: List[Term], as: Option[String])(val span: Span) extends Formula
  final case class Cmp(op: CmpOp, l: Term, r: Term)(val span: Span) extends Formula
  final case class Not(atom: Atom)(val span: Span) extends Formula
  final case class Agg(res: String, kind: AggKind, term: Term, body: List[Formula])(val span: Span) extends Formula
  final case class Disj(alts: List[List[Formula]])(val span: Span) extends Formula

  /** Use of a formula function (meta application of type ⇑prop), before meta evaluation. */
  final case class Splice(m: MExpr)(val span: Span) extends Formula

/** A formula function expansion, recorded for diagnostics. */
final case class Expansion(fn: String, use: Span, body: Span)

final case class Rule(name: Option[String], heads: List[Term], body: List[Formula])(
    val span: Span,
    val origin: Origin,
    val expansions: List[Expansion] = Nil
):
  def withParts(heads: List[Term] = heads, body: List[Formula] = body, name: Option[String] = name): Rule =
    Rule(name, heads, body)(span, origin, expansions)

final case class Query(body: List[Formula])(val span: Span, val origin: Origin, val expansions: List[Expansion] = Nil):
  def withBody(b: List[Formula]): Query = Query(b)(span, origin, expansions)

final case class ModeSpec(inputs: List[(Boolean, Option[String], Span)])

enum DirKind:
  case ModeD(spec: ModeSpec)
  /** The measure variables (several for a lexicographic measure) and the call pattern. */
  case TerminatesVar(vs: List[String], args: List[Term])

  /** The measure labels (several for a lexicographic measure). */
  case TerminatesLabel(labels: List[String])
  case Partial, Open, Input, Output
  case Derivations
  case NameHint(v: String)

/** An object directive. `target` is the relation; for `%derivations @r` the rule name is in `rule`. */
final case class Directive(kind: DirKind, target: Option[RelRef], rule: Option[String])(val span: Span, val origin: Origin)

/** Edge `τ <: a`. */
final case class Edge(sub: OType, sup: TypeSym)(val span: Span, val origin: Origin)

/** A monomorphic (after `monomorphize`) object program (Figure 2). */
final class ObjProgram(
    var types: Vector[TypeSym],
    var rels: Vector[RelSym],
    var edges: Vector[Edge],
    var rules: Vector[Rule],
    var queries: Vector[Query],
    var directives: Vector[Directive]
):
  def copyWith(rules: Vector[Rule] = rules, queries: Vector[Query] = queries, rels: Vector[RelSym] = rels): ObjProgram =
    ObjProgram(types, rels, edges, rules, queries, directives)
