package hugin.compiler

import hugin.util.Span
import scala.collection.mutable

/** What a name declares, for tooling (hover, outline, completion, semantic tokens). */
enum SymKind:
  /** `a : type.` or `a : type <: b.` (possibly a family). */
  case ObjType

  /** `a : type = { l : t, ... }.`: a relation whose fact type is `a`. */
  case Struct

  /** `c : τ̄ -> rel.` */
  case Rel

  /** `c : τ̄ -> a.` with `a` open. */
  case Ctor

  /** `n : type = τ.`, or a meta function computing an object type. */
  case TypeDef

  /** `f : τ̄ -> prop` with clauses or a definition. */
  case FormulaFn

  /** Any other meta definition (constants, functions, signatures, modules, functors, inductive types). */
  case MetaDef

  /** Parameters of meta functions and lambdas (including implicit type parameters). */
  case MetaParam

  /** `int`, `float`, `string`. */
  case BaseType

  def describe: String = this match
    case ObjType => "object type"
    case Struct => "struct"
    case Rel => "relation"
    case Ctor => "constructor"
    case TypeDef => "type definition"
    case FormulaFn => "formula function"
    case MetaDef => "meta definition"
    case MetaParam => "meta parameter"
    case BaseType => "base type"

/** A declared name, for tooling: its name, what it declares, the position of its name and of its whole
 *  declaration. Symbols are equal if these are (a symbol is recorded again by every compilation). */
final case class Sym(name: String, kind: SymKind, span: Span, extent: Span)

/** What the compiler learned about positions in the source, for tooling (hover, go to definition, find
 *  references, completion, document symbols). Filled by the elaborator (name resolution, declarations,
 *  scopes), staging (quotes, splices and persisted values, family instances) and the object typer (types
 *  of object variables). */
final class SemanticIndex:
  import SemanticIndex.*

  /** A reference to a symbol at a span. `detail` describes the symbol as seen at this reference. `isUse`
   *  is false for references that do not use the symbol, such as a `%mode` directive naming a formula
   *  function. */
  final case class Reference(span: Span, sym: Sym, detail: Option[String], isUse: Boolean)

  /** An occurrence of the object variable `name` with its inferred type. `item` is the span of the rule
   *  or query the variable belongs to (its scope); `name` is the internal name, unique within the item. */
  final case class VarOccurrence(span: Span, name: String, display: String, tpe: String, item: Span)

  /** How the code at `span` crossed between the levels when it was staged, and the value it had (printed).
   *  Code in a functor or formula function is staged once per application, so a span can have several. */
  final case class Staged(span: Span, stage: Stage, value: String)

  /** A family instance `name` (`len[int]`) of the family declared at `family`; `use` is the span of the
   *  object code that uses it. */
  final case class Instance(family: Span, name: String, use: Span)

  /** The names visible in the source extent `extent` (a module body or a file), innermost scope first. */
  final case class ScopeExtent(extent: Span, names: List[Sym])

  private val refs = mutable.ArrayBuffer.empty[Reference]
  private val stagings = mutable.LinkedHashSet.empty[Staged]
  private val instanceSet = mutable.LinkedHashSet.empty[Instance]
  private val vars = mutable.LinkedHashSet.empty[VarOccurrence]
  private val syms = mutable.LinkedHashSet.empty[Sym]
  private val descriptions = mutable.HashMap.empty[Sym, String]
  private val memberLists = mutable.HashMap.empty[Sym, List[Sym]]
  private val labelLists = mutable.HashMap.empty[Sym, List[String]]
  private val scopeExtents = mutable.ArrayBuffer.empty[ScopeExtent]
  private val directiveSyms = mutable.LinkedHashSet.empty[Sym]

  /** What the elaborator learned about the meta level (types, stages, holes), for language servers. */
  val meta: MetaIndex = MetaIndex()

  /** The names of the program's top level and of the prelude (where no recorded extent applies). */
  var topLevel: List[Sym] = Nil

  /** While set, references and variables are not recorded (code elaborated again, whose references were
   *  recorded the first time: the module that a module-wide directive rewrites). */
  var muted: Boolean = false

  def reference(span: Span, sym: Sym, detail: Option[String] = None, isUse: Boolean = true): Unit =
    if span.exists && sym.kind != SymKind.BaseType && !muted then
      refs += Reference(span, sym, detail, isUse)
      syms += sym

  def declare(sym: Sym): Unit = if sym.span.exists then syms += sym

  /** A meta function that can be applied as a directive `%d` (completion after `%`). */
  def directive(sym: Sym): Unit = directiveSyms += sym
  def isDirective(sym: Sym): Boolean = directiveSyms(sym)

  def variable(span: Span, name: String, display: String, tpe: String, item: Span): Unit =
    if span.exists && !muted then vars += VarOccurrence(span, name, display, tpe, item)

  def describe(sym: Sym, text: String): Unit = descriptions(sym) = text

  /** The members of a module-valued symbol (completion after `m.`). */
  def members(sym: Sym, ms: List[Sym]): Unit = memberLists(sym) = ms

  /** The column labels of a relation or constructor (completion in named patterns). */
  def labels(sym: Sym, ls: List[String]): Unit = if ls.nonEmpty then labelLists(sym) = ls

  def staged(span: Span, stage: Stage, value: String): Unit = if span.exists then stagings += Staged(span, stage, value)

  def instance(family: Span, name: String, use: Span = Span.NoSpan): Unit =
    if family.exists then instanceSet += Instance(family, name, use)

  def scope(extent: Span, names: List[Sym]): Unit = if extent.exists then scopeExtents += ScopeExtent(extent, names)

  /** Adds everything recorded in `other` (the index of a part elaborated apart), after what is here. */
  def include(other: SemanticIndex): Unit =
    refs ++= other.refs.map(r => Reference(r.span, r.sym, r.detail, r.isUse))
    stagings ++= other.stagings.map(s => Staged(s.span, s.stage, s.value))
    instanceSet ++= other.instanceSet.map(i => Instance(i.family, i.name, i.use))
    vars ++= other.vars.map(v => VarOccurrence(v.span, v.name, v.display, v.tpe, v.item))
    syms ++= other.syms
    descriptions ++= other.descriptions
    memberLists ++= other.memberLists
    labelLists ++= other.labelLists
    scopeExtents ++= other.scopeExtents.map(s => ScopeExtent(s.extent, s.names))
    directiveSyms ++= other.directiveSyms
    meta.include(other.meta)
    if other.topLevel.nonEmpty then topLevel = other.topLevel

  def references: Seq[Reference] = refs.toSeq
  def variables: Seq[VarOccurrence] = vars.toSeq
  def staging: Seq[Staged] = stagings.toSeq
  def instances: Seq[Instance] = instanceSet.toSeq

  /** All declared or referenced symbols with a source position. */
  def symbols: Seq[Sym] = syms.toSeq
  def description(sym: Sym): Option[String] = descriptions.get(sym)
  def membersOf(sym: Sym): List[Sym] = memberLists.getOrElse(sym, Nil)
  def labelsOf(sym: Sym): List[String] = labelLists.getOrElse(sym, Nil)
  def scopes: Seq[ScopeExtent] = scopeExtents.toSeq

object SemanticIndex:
  /** The staging of object code inside meta code (reference: meta/staging). */
  enum Stage:
    /** Object code passed where meta code is expected becomes a code value `⟨t⟩`. */
    case Quoted

    /** A meta value of code (`⇑τ`, `⇑prop`) used in object code is inserted, `$t`. */
    case Spliced

    /** A compile-time primitive used in object code is embedded as a literal (cross-stage persistence). */
    case Persisted
