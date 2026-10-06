package hugin.compiler

import hugin.meta.{Sym, SymKind}
import hugin.util.Span
import scala.collection.mutable

/** What the compiler learned about positions in the source, for tooling (hover, go to definition, find
 *  references, document symbols). Filled by the typer (name resolution) and the object typer (types of
 *  object variables). */
final class SemanticIndex:
  /** A use of a symbol at a span. */
  final case class Reference(span: Span, sym: Sym)

  /** An object variable occurrence and its inferred type. */
  final case class VarOccurrence(span: Span, name: String, tpe: String)

  private val refs = mutable.ArrayBuffer.empty[Reference]
  private val vars = mutable.ArrayBuffer.empty[VarOccurrence]
  private val syms = mutable.LinkedHashSet.empty[Sym]
  private val descriptions = mutable.HashMap.empty[Sym, String]

  def reference(span: Span, sym: Sym): Unit =
    if span.exists && sym.kind != SymKind.PreludeType then
      refs += Reference(span, sym)
      syms += sym

  def declare(sym: Sym): Unit = if sym.span.exists then syms += sym

  def variable(span: Span, name: String, tpe: String): Unit = if span.exists then vars += VarOccurrence(span, name, tpe)

  def describe(sym: Sym, text: String): Unit = descriptions(sym) = text

  def references: Seq[Reference] = refs.toSeq
  def variables: Seq[VarOccurrence] = vars.toSeq

  /** All declared or referenced symbols with a source position. */
  def symbols: Seq[Sym] = syms.toSeq
  def description(sym: Sym): Option[String] = descriptions.get(sym)
