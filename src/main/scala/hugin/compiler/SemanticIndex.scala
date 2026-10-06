package hugin.compiler

import hugin.meta.{Scope, Sym, SymKind}
import hugin.util.Span
import scala.collection.mutable

/** What the compiler learned about positions in the source, for tooling (hover, go to definition, find
 *  references, completion, document symbols). Filled by the typer (name resolution, scopes) and the
 *  object typer (types of object variables). */
final class SemanticIndex:
  /** A use of a symbol at a span. `detail` describes the symbol as seen at this use, e.g. with the type
   *  instantiated through a module path (`roads.path : city -> city -> rel`). */
  final case class Reference(span: Span, sym: Sym, detail: Option[String])

  /** An occurrence of the object variable `name` with its inferred type. `item` is the span of the rule
   *  or query the variable belongs to (its scope); `name` is the internal name, unique within the item. */
  final case class VarOccurrence(span: Span, name: String, display: String, tpe: String, item: Span)

  private val refs = mutable.ArrayBuffer.empty[Reference]
  private val vars = mutable.LinkedHashSet.empty[VarOccurrence]
  private val syms = mutable.LinkedHashSet.empty[Sym]
  private val descriptions = mutable.HashMap.empty[Sym, String]
  private val scopeExtents = mutable.ArrayBuffer.empty[(Span, Scope)]

  def reference(span: Span, sym: Sym, detail: Option[String] = None): Unit =
    if span.exists && sym.kind != SymKind.PreludeType then
      refs += Reference(span, sym, detail)
      syms += sym

  def declare(sym: Sym): Unit = if sym.span.exists then syms += sym

  def variable(span: Span, name: String, display: String, tpe: String, item: Span): Unit =
    if span.exists then vars += VarOccurrence(span, name, display, tpe, item)

  def describe(sym: Sym, text: String): Unit = descriptions(sym) = text

  /** Records the source extent of a scope (a module body or the program). */
  def scope(span: Span, scope: Scope): Unit = if span.exists then scopeExtents += ((span, scope))

  def references: Seq[Reference] = refs.toSeq
  def variables: Seq[VarOccurrence] = vars.toSeq

  /** All declared or referenced symbols with a source position. */
  def symbols: Seq[Sym] = syms.toSeq
  def description(sym: Sym): Option[String] = descriptions.get(sym)
  def scopes: Seq[(Span, Scope)] = scopeExtents.toSeq
