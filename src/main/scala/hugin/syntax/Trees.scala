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
    // by code points (an unpaired surrogate is one), as `String.codePoints` counts them
    var i = 0
    while i < s.length do
      val cp = s.codePointAt(i)
      cp match
        case '"' => sb ++= "\\\""
        case '\\' => sb ++= "\\\\"
        case '\n' => sb ++= "\\n"
        case '\t' => sb ++= "\\t"
        case c if c < 0x20 || c == 0x7f => sb ++= f"\\u{$c%x}"
        case c => sb.appendAll(Character.toChars(c))
      i += Character.charCount(cp)
    sb += '"'
    sb.toString

enum AggKind:
  case Count, Sum, Min, Max
  def show: String = toString.toLowerCase

/** The kind of a bound column (`min τ` / `max τ`, reference: object/bound-columns): it keeps the least (greatest)
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

  /** `()`: Agda's absurd pattern, for a position none of whose constructors can occur (reference:
   *  meta/clauses). It is allowed only in the patterns of a clause. */
  final case class Absurd()(val span: Span) extends Tree

  /** The right-hand side of an absurd clause `f p̄.`, which has none (`span` is empty, at the period). */
  final case class Absent()(val span: Span) extends Tree
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
    /** `data` is a keyword only as the whole type of a declaration (`list A : data.`, a shared data
     *  declaration); elsewhere it is a name. */
    case Type, Rel, Prop, Data
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

  // ---- the meta level's own syntax (reference: meta/index)

  /** `$t`: an explicit splice (reference: meta/staging), normally inferred; inside a quote, a hole. */
  final case class SpliceE(arg: Tree)(val span: Span) extends Tree

  /** `⇑t` (ASCII `^t`): the lift of an object type to the meta level; normally inferred. */
  final case class LiftE(arg: Tree)(val span: Span) extends Tree

  /** `<t>`: an explicit staging quote, object code `t` as a meta value of type `⇑A` (reference:
   *  meta/staging); normally inferred. */
  final case class CodeQuote(arg: Tree)(val span: Span) extends Tree

  /** `?` or `?name`: a typed hole, an expression still to be written (reference: meta/functions). */
  final case class Hole(name: Option[String])(val span: Span) extends Tree

  /** `{A B : T}` in front of `->`: implicit binders (only as the domain of an [[ImplicitPi]]). */
  final case class ImplicitBinder(names: List[Tree], tpe: Tree)(val span: Span) extends Tree

  /** `{A B : T} -> B`: an implicit Π type. */
  final case class ImplicitPi(names: List[Tree], dom: Tree, cod: Tree)(val span: Span) extends Tree

  // ---- reflection (reference: reflection)

  /** `[e₁, …, eₙ]`: a meta list (`[]` is the empty one). */
  final case class ListLit(elems: List[Tree])(val span: Span) extends Tree

  /** `e :: es`: a meta list with head `e`. */
  final case class ConsE(head: Tree, tail: Tree)(val span: Span) extends Tree

  /** `'( … )`: a reflection quote, object syntax as data (reference: reflection). Its content is a sequence
   *  of entries as in a file: rules and facts ([[Rule]], a fact's single head unsplit, so that `p X, q X`
   *  without `:-` is one formula) and queries ([[Query]]), separated by periods; `terminated` if the last
   *  entry ends with a period. Which syntactic category the content denotes (a module, a rule, an item, a
   *  formula, a term, …) is given by the expected type. */
  final case class Quote(entries: List[Item], terminated: Boolean)(val span: Span) extends Tree

  /** `$..xs`: a sequence hole (arguments, body formulas, list elements); only inside a quote. */
  final case class SpliceSeq(arg: Tree)(val span: Span) extends Tree

  /** `$f[t̄]`: a higher-order hole, `f` applied to object terms (variables bound by an aggregate); only
   *  inside a quote. */
  final case class SpliceHO(fn: Tree, args: List[Tree])(val span: Span) extends Tree

  /** A reference to an object constant that is already resolved (generated by reflection, never parsed):
   *  `id` is the global, `name` how it is shown. */
  final case class SymRef(id: Int, name: String)(val span: Span) extends Tree

  /** An object variable by name inside reflected object code (never parsed): it is the variable of the
   *  enclosing item with that name. */
  final case class NamedVar(name: String)(val span: Span) extends Tree

  /** A piece of syntax with a syntax error (reported by the parser): something missing (no parts, an empty
   *  span where it should be), or a construct that is damaged (unclosed, followed by skipped tokens), with
   *  the trees that parsed in it. Later phases do not elaborate an item that contains one; they drop it
   *  without further diagnostics ([[TreeOps.hasSyntaxErrors]], `docs/PARSER.md` §5). */
  final case class ErrorTree(parts: List[Tree])(val span: Span) extends Tree

  /** `+e -t +`: mode items as a directive argument (`%demand typed +e +g -t.`), elaborated to the prelude's
   *  `modes` data (reference: directives). */
  final case class ModeArgs(items: List[ModeItem])(val span: Span) extends Tree

  final case class Field(label: Ident, value: Tree)

  enum SigEntry:
    /** `l : τ`. */
    case FieldDecl(label: Ident, tpe: Tree)
    case Complete(label: Ident, span: Span)

  final case class ModeItem(input: Boolean, label: Option[Ident], span: Span)

  /** Parameters of declarations: `X` (type parameter / untyped) or `(x : T)`. */
  enum Param:
    case VarParam(v: VarRef)
    case Typed(name: Tree, tpe: Tree, sp: Span)

    /** A parameter that is neither (a syntax error, reported by the parser). */
    case Malformed(tree: Tree)
    def span: Span = this match
      case VarParam(v) => v.span
      case Typed(_, _, s) => s
      case Malformed(t) => t.span
    def nameString: String = this match
      case VarParam(v) => v.name
      case Typed(n: Ident, _, _) => n.name
      case Typed(n: VarRef, _, _) => n.name
      case Typed(_, _, _) | Malformed(_) => "?"

  sealed trait Item:
    def span: Span

  /** `name param* : type [<: sup] [= defn].` */
  final case class Decl(name: Ident, params: List[Param], tpe: Tree, sup: Option[Tree], defn: Option[Tree])(
      val span: Span
  ) extends Item

  /** `name param* = expr.` */
  final case class Def(name: Ident, params: List[Param], rhs: Tree)(val span: Span) extends Item

  /** `f p̄ = e.` with patterns that are not all variables, or with a `where` block of local definitions:
   *  an equational clause of a meta function (reference: meta/clauses). An absurd clause `f p̄.`, whose
   *  patterns contain `()`, has the right-hand side [[Absent]]. */
  final case class Clause(lhs: Tree, rhs: Tree, where: List[Item] = Nil)(val span: Span) extends Item

  /** `type <: type.` */
  final case class SubEdge(sub: Tree, sup: Tree)(val span: Span) extends Item
  final case class Rule(name: Option[Ident], heads: List[Tree], body: Option[Tree])(val span: Span) extends Item
  final case class Query(body: Tree)(val span: Span) extends Item

  /** A directive `%kind …` (reference: directives). `kindSpan` is the span of `%kind`. */
  final case class Directive(kind: String, args: DirArgs)(val span: Span, val kindSpan: Span) extends Item

  enum DirArgs:
    /** `%d a₁ … aₙ.`: the application of the meta function `d`; with `decl`, the prefix form `%d a₁ … aₙ`
     *  attached to the declaration of `decl` that follows it. */
    case Apply(args: List[Tree], decl: Option[Ident])

    /** `%infix assoc p name`: handled by the parser. */
    case Infix(assoc: String, prec: Int, name: Ident)

    /** `%use m.` or `%use m (x, y).` (reference: modules): opens the fields of the module `m` (an
     *  expression; `%use "f"` is `%use %import "f"`), or only those named, into the file's scope. */
    case Use(module: Tree, names: Option[List[Ident]])

    /** `%export S.` (reference: modules): the file's module value is ascribed the signature `S`. */
    case Export(signature: Tree)

  final case class Program(items: List[Item], span: Span):
    /** All `%import` expressions of the program, in source order. Computed once per program (trees are
     *  immutable): the standard library's parsed files are shared by every compilation of a process, and
     *  each compilation asks for their imports (`LazyStdlib`, the import graph). */
    lazy val imports: List[Import] = TreeOps.nodes(items).collect { case i: Import => i }.toList

export Trees.*
