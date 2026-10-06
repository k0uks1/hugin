package hugin.compiler

import hugin.meta.{Scope, Sym, SymKind}
import hugin.util.Span
import scala.collection.mutable

/** What the compiler learned about positions in the source, for tooling (hover, go to definition, find
 *  references, completion, document symbols). Filled by the typer (name resolution, scopes), the meta
 *  evaluator (staging), monomorphization (family instances) and the object typer (types of object
 *  variables). */
final class SemanticIndex:
  import SemanticIndex.*

  /** A reference to a symbol at a span. `detail` describes the symbol as seen at this reference, e.g. with
   *  the type instantiated through a module path (`roads.path : city -> city -> rel`). `isUse` is false for
   *  references that do not use the symbol, such as a `%mode` directive naming a formula function (a
   *  definition with no uses is reported as unused, W0003). */
  final case class Reference(span: Span, sym: Sym, detail: Option[String], isUse: Boolean)

  /** An occurrence of the object variable `name` with its inferred type. `item` is the span of the rule
   *  or query the variable belongs to (its scope); `name` is the internal name, unique within the item. */
  final case class VarOccurrence(span: Span, name: String, display: String, tpe: String, item: Span)

  /** How the code at `span` crossed between the levels when it was evaluated, and the value it had
   *  (printed). Code in a functor or formula function is evaluated once per application, so a span can
   *  have several values. */
  final case class Staged(span: Span, stage: Stage, value: String)

  /** A family instance `name` (`len[int]`) of the family declared at `family`; `use` is the span of the
   *  application that requested it, or no span for an instance requested by a type or another instance. */
  final case class Instance(family: Span, name: String, use: Span)

  private val refs = mutable.ArrayBuffer.empty[Reference]
  private val stagings = mutable.LinkedHashSet.empty[Staged]
  private val instanceSet = mutable.LinkedHashSet.empty[Instance]
  private val vars = mutable.LinkedHashSet.empty[VarOccurrence]
  private val syms = mutable.LinkedHashSet.empty[Sym]
  private val descriptions = mutable.HashMap.empty[Sym, String]
  private val scopeExtents = mutable.ArrayBuffer.empty[(Span, Scope)]

  def reference(span: Span, sym: Sym, detail: Option[String], isUse: Boolean): Unit =
    if span.exists && sym.kind != SymKind.BaseType then
      refs += Reference(span, sym, detail, isUse)
      syms += sym

  def declare(sym: Sym): Unit = if sym.span.exists then syms += sym

  def variable(span: Span, name: String, display: String, tpe: String, item: Span): Unit =
    if span.exists then vars += VarOccurrence(span, name, display, tpe, item)

  def describe(sym: Sym, text: String): Unit = descriptions(sym) = text

  def staged(span: Span, stage: Stage, value: String): Unit = if span.exists then stagings += Staged(span, stage, value)

  def instance(family: Span, name: String, use: Span = Span.NoSpan): Unit =
    if family.exists then instanceSet += Instance(family, name, use)

  /** Records the source extent of a scope (a module body or the program). */
  def scope(span: Span, scope: Scope): Unit = if span.exists then scopeExtents += ((span, scope))

  /** Adds everything recorded in `other` (the index of a library elaborated apart), after what is here. */
  def include(other: SemanticIndex): Unit =
    refs ++= other.refs.map(r => Reference(r.span, r.sym, r.detail, r.isUse))
    stagings ++= other.stagings.map(s => Staged(s.span, s.stage, s.value))
    instanceSet ++= other.instanceSet.map(i => Instance(i.family, i.name, i.use))
    vars ++= other.vars.map(v => VarOccurrence(v.span, v.name, v.display, v.tpe, v.item))
    syms ++= other.syms
    descriptions ++= other.descriptions
    scopeExtents ++= other.scopeExtents

  def references: Seq[Reference] = refs.toSeq
  def variables: Seq[VarOccurrence] = vars.toSeq
  def staging: Seq[Staged] = stagings.toSeq
  def instances: Seq[Instance] = instanceSet.toSeq

  /** All declared or referenced symbols with a source position. */
  def symbols: Seq[Sym] = syms.toSeq
  def description(sym: Sym): Option[String] = descriptions.get(sym)
  def scopes: Seq[(Span, Scope)] = scopeExtents.toSeq

object SemanticIndex:
  /** The staging of object code inside meta code (Section 3.2). */
  enum Stage:
    /** An object term or formula passed where meta code is expected becomes a code value `⟨t⟩`. */
    case Quoted

    /** A meta value of code (`⇑τ`, `⇑prop`) used in object code is inserted, `~(m)`. */
    case Spliced

    /** A compile-time primitive used in object code is embedded as a literal (cross-stage persistence). */
    case Persisted
