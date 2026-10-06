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
    case Type, Mod, Rel, Prop
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
  final case class Conj(lhs: Tree, rhs: Tree)(val span: Span) extends Tree
  final case class Disj(lhs: Tree, rhs: Tree)(val span: Span) extends Tree
  final case class Parens(inner: Tree)(val span: Span) extends Tree

  /** `%builtin int`: a base type provided by the implementation (used by the prelude). */
  final case class Builtin(name: Ident)(val span: Span) extends Tree

  /** `%import "path"`: the module value of another source file (Section 4.3, M-Body). */
  final case class Import(path: String)(val span: Span, val pathSpan: Span) extends Tree

  final case class Field(label: Ident, value: Tree)

  enum SigEntry:
    case FieldDecl(label: Ident, tpe: Tree)
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

  /** `name param* : type [<: sup] [= defn].` and `%abbrev`. */
  final case class Decl(name: Ident, params: List[Param], tpe: Tree, sup: Option[Tree], defn: Option[Tree], abbrev: Boolean)(val span: Span)
      extends Item

  /** `name param* = expr.` */
  final case class Def(name: Ident, params: List[Param], rhs: Tree)(val span: Span) extends Item

  /** `type <: type.` */
  final case class SubEdge(sub: Tree, sup: Tree)(val span: Span) extends Item
  final case class Rule(name: Option[Ident], heads: List[Tree], body: Option[Tree])(val span: Span) extends Item
  final case class Query(body: Tree)(val span: Span) extends Item
  final case class Directive(kind: String, args: DirArgs)(val span: Span, val kindSpan: Span) extends Item

  enum DirArgs:
    case Mode(target: Tree, modes: List[ModeItem])
    case TerminatesVar(v: VarRef, target: Tree, args: List[Tree])
    case TerminatesLabel(label: Ident, target: Tree)
    case Target(target: Tree) // %partial %open %input %output %derivations
    case Infix(assoc: String, prec: Int, name: Ident)
    case NameHint(target: Tree, v: VarRef)

  final case class Program(items: List[Item], span: Span)

export Trees.*
