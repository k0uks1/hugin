package hugin.syntax

import hugin.util.Span

/** Literals shared by both levels. */
enum Literal:
  case IntL(v: Long)
  case FloatL(v: Double)
  case StrL(v: String)

  def show: String = this match
    case IntL(v) => v.toString
    case FloatL(v) => Literal.showDouble(v)
    case StrL(v) => Literal.quote(v)

object Literal:
  def showDouble(d: Double): String =
    if d.isNaN then "nan"
    else if d.isInfinite then (if d > 0 then "inf" else "-inf")
    else
      val s = d.toString
      if s.contains('.') || s.contains('E') then s else s + ".0"
  def quote(s: String): String =
    val sb = new StringBuilder("\"")
    s.codePoints().forEach { cp =>
      cp match
        case '"' => sb ++= "\\\""
        case '\\' => sb ++= "\\\\"
        case '\n' => sb ++= "\\n"
        case '\t' => sb ++= "\\t"
        case c if c < 0x20 || c == 0x7f => sb ++= f"\\u{$c%x}"
        case c => sb.appendAll(Character.toChars(c))
    }
    sb += '"'
    sb.toString

enum AggKind:
  case Count, Sum, Min, Max
  def show: String = toString.toLowerCase

/** The kind of a bound column (`min τ` / `max τ`, docs/REDESIGN.md §5.2): it keeps the least (greatest)
 *  value per key. */
enum Bound:
  case Min, Max
  def show: String = toString.toLowerCase

/** Surface syntax (untyped). Types, expressions, terms and formulas share one tree language (Figure 1). */
sealed trait Tree:
  def span: Span

object Trees:
  final case class Ident(name: String)(val span: Span) extends Tree // lowercase name
  final case class VarRef(name: String)(val span: Span) extends Tree // uppercase variable
  final case class Wildcard()(val span: Span) extends Tree
  final case class RuleRef(name: String)(val span: Span) extends Tree // @r (in directives)
  final case class Lit(value: Literal)(val span: Span) extends Tree
  final case class Select(qual: Tree, name: String)(val span: Span, val nameSpan: Span) extends Tree
  final case class Apply(fn: Tree, arg: Tree)(val span: Span) extends Tree

  /** Binary operators: arithmetic `+ - * / ^`, comparisons, and user `%infix` names (resolved to Apply). */
  final case class Infix(op: String, lhs: Tree, rhs: Tree)(val span: Span, val opSpan: Span) extends Tree
  final case class Neg(arg: Tree)(val span: Span) extends Tree
  final case class Arrow(label: Option[Ident], dom: Tree, cod: Tree)(val span: Span) extends Tree
  final case class Union(lhs: Tree, rhs: Tree)(val span: Span) extends Tree
  enum Kw:
    case Type, Rel, Prop
  final case class Keyword(kw: Kw)(val span: Span) extends Tree
  final case class RecordType(entries: List[SigEntry])(val span: Span) extends Tree
  final case class ModuleBody(items: List[Item])(val span: Span) extends Tree

  /** `{ l = e, ... }` — record value, or (after a relation) a named pattern; `rest` marks a trailing `..`. */
  final case class RecordLit(fields: List[Field], rest: Boolean)(val span: Span) extends Tree
  final case class Lambda(param: Tree, tpe: Option[Tree], body: Tree)(val span: Span) extends Tree
  final case class As(term: Tree, v: VarRef)(val span: Span) extends Tree
  final case class Ascribe(term: Tree, tpe: Tree)(val span: Span) extends Tree
  final case class With(v: VarRef, fields: List[Field])(val span: Span) extends Tree
  final case class Not(arg: Tree)(val span: Span) extends Tree
  final case class Agg(kind: AggKind, term: Tree, body: Tree)(val span: Span) extends Tree

  /** The column type `min τ` / `max τ` of a bound column. */
  final case class BoundType(kind: Bound, tpe: Tree)(val span: Span) extends Tree
  final case class Conj(lhs: Tree, rhs: Tree)(val span: Span) extends Tree
  final case class Disj(lhs: Tree, rhs: Tree)(val span: Span) extends Tree
  final case class Parens(inner: Tree)(val span: Span) extends Tree

  /** `%builtin int`: a base type provided by the implementation (used by the prelude). */
  final case class Builtin(name: Ident)(val span: Span) extends Tree

  /** `%import "path"`: the module value of another source file (Section 4.3, M-Body). */
  final case class Import(path: String)(val span: Span, val pathSpan: Span) extends Tree

  // ---- the meta level's own syntax (docs/REDESIGN.md §6)

  /** `$t`: an explicit splice (REDESIGN §6.9); normally inferred. */
  final case class SpliceE(arg: Tree)(val span: Span) extends Tree

  /** `⇑t`: the lift of an object type to the meta level; normally inferred. */
  final case class LiftE(arg: Tree)(val span: Span) extends Tree

  /** `{A B : T}` in front of `->`: implicit binders (only as the domain of an [[ImplicitPi]]). */
  final case class ImplicitBinder(names: List[Tree], tpe: Tree)(val span: Span) extends Tree

  /** `{A B : T} -> B`: an implicit Π type. */
  final case class ImplicitPi(names: List[Tree], dom: Tree, cod: Tree)(val span: Span) extends Tree

  // ---- reflection (docs/REDESIGN.md §6.8–6.9)

  /** `[e₁, …, eₙ]`: a meta list (`[]` is the empty one). */
  final case class ListLit(elems: List[Tree])(val span: Span) extends Tree

  /** `e :: es`: a meta list with head `e`. */
  final case class ConsE(head: Tree, tail: Tree)(val span: Span) extends Tree

  /** `(h̄ :- b)`: a rule as an expression or pattern (object syntax of type `Rule`); `body` is `None` for
   *  `(h :-)`. */
  final case class RuleQuote(heads: List[Tree], body: Option[Tree])(val span: Span) extends Tree

  /** `$..xs`: a sequence hole (arguments, body formulas, list elements). */
  final case class SpliceSeq(arg: Tree)(val span: Span) extends Tree

  /** `$f[t̄]`: a higher-order hole, `f` applied to object terms (variables bound by an aggregate). */
  final case class SpliceHO(fn: Tree, args: List[Tree])(val span: Span) extends Tree

  /** A reference to an object constant that is already resolved (generated by reflection, never parsed):
   *  `id` is the global, `name` how it is shown. */
  final case class SymRef(id: Int, name: String)(val span: Span) extends Tree

  /** An object variable by name inside reflected object code (never parsed): it is the variable of the
   *  enclosing item with that name. */
  final case class NamedVar(name: String)(val span: Span) extends Tree

  final case class Field(label: Ident, value: Tree)

  enum SigEntry:
    /** `l : τ`, or `%fact l : τ̄ -> a` (a field that must be a fact constructor). */
    case FieldDecl(label: Ident, tpe: Tree, fact: Boolean = false)
    case Complete(label: Ident, span: Span)
    case ModeReq(label: Ident, modes: List[ModeItem], span: Span)

  final case class ModeItem(input: Boolean, label: Option[Ident], span: Span)

  /** Parameters of declarations: `X` (type parameter / untyped) or `(x : T)`. */
  enum Param:
    case VarParam(v: VarRef)
    case Typed(name: Tree, tpe: Tree, sp: Span)
    def span: Span = this match
      case VarParam(v) => v.span
      case Typed(_, _, s) => s
    def nameString: String = this match
      case VarParam(v) => v.name
      case Typed(n: Ident, _, _) => n.name
      case Typed(n: VarRef, _, _) => n.name
      case Typed(_, _, _) => "?"

  sealed trait Item:
    def span: Span

  /** `name param* : type [<: sup] [= defn].`, or with `%fact` (a fact constructor or struct). */
  final case class Decl(name: Ident, params: List[Param], tpe: Tree, sup: Option[Tree], defn: Option[Tree], fact: Boolean = false)(
      val span: Span
  ) extends Item

  /** `name param* = expr.` */
  final case class Def(name: Ident, params: List[Param], rhs: Tree)(val span: Span) extends Item

  /** `f p̄ = e.` with patterns that are not all variables, or with a `where` block of local definitions:
   *  an equational clause of a meta function (REDESIGN §6.4). */
  final case class Clause(lhs: Tree, rhs: Tree, where: List[Item] = Nil)(val span: Span) extends Item

  /** `type <: type.` */
  final case class SubEdge(sub: Tree, sup: Tree)(val span: Span) extends Item
  final case class Rule(name: Option[Ident], heads: List[Tree], body: Option[Tree])(val span: Span) extends Item
  final case class Query(body: Tree)(val span: Span) extends Item

  /** A directive `%kind …` (REDESIGN §7). `kindSpan` is the span of `%kind`. */
  final case class Directive(kind: String, args: DirArgs)(val span: Span, val kindSpan: Span) extends Item

  enum DirArgs:
    /** `%d a₁ … aₙ.`: the application of the meta function `d`; with `decl`, the prefix form `%d a₁ … aₙ`
     *  attached to the declaration of `decl` that follows it. */
    case Apply(args: List[Tree], decl: Option[Ident])

    /** `%mode r +l -m` (until `%demand` replaces it, REDESIGN C3). */
    case Mode(target: Tree, modes: List[ModeItem])

    /** `%infix assoc p name`: handled by the parser. */
    case Infix(assoc: String, prec: Int, name: Ident)

  final case class Program(items: List[Item], span: Span)

export Trees.*
