package hugin.lsp

import hugin.meta.SymKind
import hugin.query.{CompileKey, Compile, Database, Ide, Parse}
import hugin.util.{Diagnostic as HDiagnostic, Severity, SourceFile, Span}
import org.eclipse.lsp4j.*
import scala.jdk.CollectionConverters.*

/** The language features, answered through the [[Ide]] API and the compiler queries. Documents are keyed
 *  by their URI, which is also the path of their [[SourceFile]]. Programs (`.hgn`) get every feature;
 *  facts files (`.facts`) get syntax diagnostics. */
object Features:
  def isFacts(uri: String): Boolean = uri.endsWith(".facts")

  private def key(uri: String) = CompileKey(uri)
  private def source(uri: String)(using db: Database): SourceFile = db(Parse, uri).source
  private def offset(uri: String, pos: Position)(using Database): Int = Positions.offset(source(uri), pos)
  private def inFile(span: Span, uri: String) = span.exists && span.source.path == uri
  private def location(span: Span) = Location(span.source.path, Positions.range(span))

  // ----------------------------------------------------------------------------------------- diagnostics

  /** The compiler's diagnostics for a document. */
  def compilerDiagnostics(uri: String)(using db: Database): List[HDiagnostic] =
    val all = if isFacts(uri) then db(Parse, uri).diagnostics else Ide.diagnostics(key(uri))
    all.filter(d => !d.primarySpan.exists || d.primarySpan.source.path == uri)

  def diagnostics(uri: String)(using Database): List[Diagnostic] = compilerDiagnostics(uri).map(toLsp)

  /** The range is the primary label's; its message, the notes and the helps form the message; secondary
   *  labels and the meta-level call chain become related information. */
  def toLsp(d: HDiagnostic): Diagnostic =
    val primary = d.labels.find(_.primary).filter(_.span.exists)
    val text = (d.message :: primary.map(_.message).filter(_.nonEmpty).toList) ++
      d.notes.map("note: " + _) ++ d.helps.map("help: " + _)
    val range = primary.map(l => Positions.range(l.span)).getOrElse(Range(Position(0, 0), Position(0, 0)))
    val out = Diagnostic(range, text.mkString("\n"), severity(d.severity), "hugin")
    d.code.foreach(out.setCode)
    if d.code.exists(unnecessary) then out.setTags(List(DiagnosticTag.Unnecessary).asJava)
    val secondary = d.labels.filter(l => !l.primary && l.span.exists).map { l =>
      DiagnosticRelatedInformation(location(l.span), if l.message.nonEmpty then l.message else "related location")
    }
    val frames = d.origin.frames.filter(_.span.exists).map(f => DiagnosticRelatedInformation(location(f.span), f.description))
    if secondary.nonEmpty || frames.nonEmpty then out.setRelatedInformation((secondary ++ frames).asJava)
    out

  private def severity(s: Severity) = s match
    case Severity.Error => DiagnosticSeverity.Error
    case Severity.Warning => DiagnosticSeverity.Warning
    case Severity.Note => DiagnosticSeverity.Information

  /** Singleton variables and unused definitions are shown faded. */
  private val unnecessary = Set("W0002", "W0003")

  // ------------------------------------------------------------------------------------ position queries

  def hover(uri: String, pos: Position)(using Database): Option[Hover] =
    if isFacts(uri) then None
    else Ide.hover(key(uri), offset(uri, pos)).map(text => Hover(MarkupContent(MarkupKind.MARKDOWN, s"```hugin\n$text\n```")))

  def definition(uri: String, pos: Position)(using Database): List[Location] =
    if isFacts(uri) then Nil else Ide.definition(key(uri), offset(uri, pos)).map(location).toList

  def references(uri: String, pos: Position, includeDeclaration: Boolean)(using Database): List[Location] =
    if isFacts(uri) then Nil
    else
      val off = offset(uri, pos)
      val decl = Ide.definition(key(uri), off)
      Ide.references(key(uri), off).filter(sp => includeDeclaration || !decl.contains(sp)).map(location)

  // ------------------------------------------------------------------------------------------- outline

  /** The outline, nested by enclosing definitions (module bodies). */
  def documentSymbols(uri: String)(using Database): List[DocumentSymbol] =
    if isFacts(uri) then return Nil
    final class Node(val sym: hugin.query.DocumentSymbol):
      val children = scala.collection.mutable.ListBuffer.empty[Node]
      def extent: Span = children.foldLeft(sym.extent)((sp, c) => sp.to(c.extent))
      def toLsp: DocumentSymbol =
        val out = DocumentSymbol(sym.name, symbolKind(sym.kind), Positions.range(extent), Positions.range(sym.span), sym.kind.describe)
        out.setChildren(children.map(_.toLsp).asJava)
        out
    val roots = scala.collection.mutable.ListBuffer.empty[Node]
    val all = scala.collection.mutable.ListBuffer.empty[Node]
    for s <- Ide.symbols(key(uri)) do
      val node = Node(s)
      val parent = s.container.flatMap { c =>
        all.filter(n => n.sym.name == c && n.sym.kind == SymKind.MetaDef && n.sym.extent.start <= s.span.start && s.span.end <= n.sym.extent.end)
          .minByOption(n => n.sym.extent.end - n.sym.extent.start)
      }
      parent.fold(roots)(_.children) += node
      all += node
    roots.map(_.toLsp).toList

  private def symbolKind(k: SymKind): SymbolKind = k match
    case SymKind.ObjType | SymKind.PreludeType => SymbolKind.Class
    case SymKind.Struct => SymbolKind.Struct
    case SymKind.Rel => SymbolKind.Function
    case SymKind.Ctor => SymbolKind.Constructor
    case SymKind.TypeDef => SymbolKind.TypeParameter
    case SymKind.FormulaFn => SymbolKind.Method
    case SymKind.MetaDef => SymbolKind.Module
    case SymKind.MetaParam => SymbolKind.Variable

  // ------------------------------------------------------------------------------------ semantic tokens

  /** Token types of the semantic tokens legend; a token's type is its index. */
  val tokenTypes: List[String] = List(
    SemanticTokenTypes.Namespace, // meta definitions: modules, functors, signatures, constants
    SemanticTokenTypes.Type, // object types, type definitions, base types
    SemanticTokenTypes.Struct, // structs
    SemanticTokenTypes.Function, // relations
    SemanticTokenTypes.EnumMember, // constructors
    SemanticTokenTypes.Macro, // formula functions (expanded hygienically)
    SemanticTokenTypes.Parameter, // meta parameters
    SemanticTokenTypes.Variable // object variables
  )
  val tokenModifiers: List[String] = List(SemanticTokenModifiers.Declaration)

  private def tokenType(k: SymKind): Int = k match
    case SymKind.MetaDef => 0
    case SymKind.ObjType | SymKind.TypeDef | SymKind.PreludeType => 1
    case SymKind.Struct => 2
    case SymKind.Rel => 3
    case SymKind.Ctor => 4
    case SymKind.FormulaFn => 5
    case SymKind.MetaParam => 6

  /** Semantic tokens from the semantic index: declarations, resolved names and object variables, encoded
   *  relative to the previous token as the protocol requires. */
  def semanticTokens(uri: String)(using db: Database): SemanticTokens =
    if isFacts(uri) then return SemanticTokens(List.empty[Integer].asJava)
    val index = db(Compile, key(uri)).index
    val decls = index.symbols.map(s => (s.span, s.name, tokenType(s.kind), 1))
    val uses = index.references.map(r => (r.span, r.sym.name, tokenType(r.sym.kind), 0))
    val vars = index.variables.map(v => (v.span, v.name, 7, 0))
    val tokens = (decls ++ uses ++ vars)
      .filter((sp, name, _, _) => inFile(sp, uri) && sp.text == name)
      .sortBy((sp, _, _, mods) => (sp.start, -mods))
    val data = scala.collection.mutable.ArrayBuffer.empty[Integer]
    var prevLine = 0
    var prevChar = 0
    var prevEnd = -1
    for (sp, _, tpe, mods) <- tokens if sp.start >= prevEnd do
      val pos = Positions.position(sp.source, sp.start)
      val line = pos.getLine
      val char = pos.getCharacter
      data ++= List(line - prevLine, if line == prevLine then char - prevChar else char, sp.end - sp.start, tpe, mods).map(Int.box)
      prevLine = line
      prevChar = char
      prevEnd = sp.end
    SemanticTokens(data.asJava)

  // --------------------------------------------------------------------------------------- code actions

  /** Quick fixes for the diagnostics overlapping a range: `_` for singleton variables (W0002), and the
   *  missing labels of a named pattern (E0301). */
  def codeActions(uri: String, range: Range)(using Database): List[CodeAction] =
    if isFacts(uri) then return Nil
    val src = source(uri)
    val (from, to) = (Positions.offset(src, range.getStart), Positions.offset(src, range.getEnd))
    for
      d <- compilerDiagnostics(uri)
      sp = d.primarySpan
      if sp.exists && sp.start <= to && from <= sp.end
      (title, edit, preferred) <- fixes(d, sp)
    yield
      val action = CodeAction(title)
      action.setKind(CodeActionKind.QuickFix)
      action.setDiagnostics(List(toLsp(d)).asJava)
      action.setEdit(WorkspaceEdit(Map(uri -> List(edit).asJava).asJava))
      action.setIsPreferred(preferred)
      action

  private def fixes(d: HDiagnostic, sp: Span): List[(String, TextEdit, Boolean)] =
    def replace(text: String) = TextEdit(Positions.range(sp), text)
    def insert(at: Int, text: String) = TextEdit(Range(Positions.position(sp.source, at), Positions.position(sp.source, at)), text)
    d.code match
      case Some("W0002") =>
        val v = sp.text
        List((s"Replace `$v` with `_`", replace("_"), true), (s"Rename `$v` to `_$v`", replace(s"_$v"), false))
      case Some("E0301") =>
        // the primary label lists the missing labels: missing `a`, `b`
        val missing = "`([^`]+)`".r.findAllMatchIn(d.labels.find(_.primary).fold("")(_.message)).map(_.group(1)).toList
        val text = sp.text
        val (open, close) = (text.indexOf('{'), text.lastIndexOf('}'))
        if missing.isEmpty || open < 0 || close < open then Nil
        else
          // insert after the last field, before the closing brace
          val at = sp.start + text.lastIndexWhere(!_.isWhitespace, close - 1) + 1
          val sep = if text.substring(open + 1, close).isBlank then "" else ", "
          // in a body the missing columns are ignored (`_`); a head needs a value, here a variable named after the label
          val inBody = d.helps.exists(_.contains("`..`"))
          def value(l: String) = if inBody then "_" else l.capitalize
          val add = ("Add the missing labels", insert(at, sep + missing.map(l => s"$l = ${value(l)}").mkString(", ")), true)
          if inBody then List(add, ("Ignore the missing labels with `..`", insert(at, sep + ".."), false)) else List(add)
      case _ => Nil
