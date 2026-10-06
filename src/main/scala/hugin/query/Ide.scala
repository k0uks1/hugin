package hugin.query

import hugin.meta.{Sym, SymKind}
import hugin.util.*

/** A declaration in a document outline. */
final case class DocumentSymbol(name: String, kind: String, span: Span, container: Option[String])

/** Position-based queries for tooling (hover, go to definition, find references, outline). Positions are
 *  character offsets into the file's text. */
object Ide:
  private def compiled(key: CompileKey)(using db: Database): Compiled = db(Compile, key)

  private def covers(span: Span, path: String, offset: Int): Boolean =
    span.exists && span.source.path == path && span.start <= offset && offset <= span.end

  /** The symbol referenced or declared at an offset (the innermost one). */
  def symbolAt(key: CompileKey, offset: Int)(using db: Database): Option[Sym] =
    val index = compiled(key).index
    val uses = index.references.filter(r => covers(r.span, key.path, offset)).map(r => (r.span, r.sym))
    val decls = index.symbols.filter(s => covers(s.span, key.path, offset)).map(s => (s.span, s))
    (uses ++ decls).sortBy((sp, _) => sp.end - sp.start).headOption.map(_._2)

  /** Hover text: the description of a symbol, or the inferred type of an object variable. */
  def hover(key: CompileKey, offset: Int)(using db: Database): Option[String] =
    val index = compiled(key).index
    symbolAt(key, offset).flatMap(index.description).orElse {
      index.variables
        .filter(v => covers(v.span, key.path, offset))
        .sortBy(v => v.span.end - v.span.start)
        .headOption
        .map(v => s"variable ${v.name} : ${v.tpe}")
    }

  /** Where the symbol at an offset is declared. */
  def definition(key: CompileKey, offset: Int)(using db: Database): Option[Span] =
    symbolAt(key, offset).map(_.span).filter(_.exists)

  /** The declaration and all uses of the symbol at an offset, in source order. */
  def references(key: CompileKey, offset: Int)(using db: Database): List[Span] =
    symbolAt(key, offset).toList.flatMap { s =>
      val uses = compiled(key).index.references.filter(_.sym eq s).map(_.span)
      (s.span +: uses).filter(_.exists).distinct.sortBy(sp => (sp.source.path, sp.start))
    }

  private val outlineKinds: Set[SymKind] =
    Set(SymKind.ObjType, SymKind.Struct, SymKind.Rel, SymKind.Ctor, SymKind.TypeDef, SymKind.FormulaFn, SymKind.MetaDef)

  /** The declarations of a file, each with its enclosing definition (for nested module bodies). */
  def symbols(key: CompileKey)(using db: Database): List[DocumentSymbol] =
    val syms = compiled(key).index.symbols.filter(s => outlineKinds(s.kind) && s.span.exists && s.span.source.path == key.path)
    val containers = syms.filter(s => s.kind == SymKind.MetaDef).flatMap(s => s.decl.map(d => (s, d.span)))
    syms.toList
      .sortBy(_.span.start)
      .map { s =>
        val enclosing = containers
          .filter((c, sp) => (c ne s) && sp.start <= s.span.start && s.span.end <= sp.end)
          .sortBy((_, sp) => sp.end - sp.start)
          .headOption
          .map(_._1.name)
        DocumentSymbol(s.name, s.kind.describe, s.span, enclosing)
      }

  def diagnostics(key: CompileKey)(using db: Database): List[Diagnostic] = compiled(key).diagnostics
