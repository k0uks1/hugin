package hugin.lsp

import hugin.meta.SymKind
import hugin.query.{CompileKey, Compile, Database, FileDiagnostics, Ide, Parse, SourceText}
import hugin.util.{Diagnostic as HDiagnostic, Severity, SourceFile, Span}
import hugin.util.diagnostics.Suggestion
import org.eclipse.lsp4j.*
import scala.collection.mutable
import scala.jdk.CollectionConverters.*
import scala.util.control.NonFatal

/** The language features of the server, answered through the [[hugin.query.Ide]] API and the compiler queries, in
 *  terms of the protocol: URIs, 0-based UTF-16 positions and lsp4j's data types.
 *
 *  Documents are keyed in the database by their path (see [[Uris]]); an open document's text is its
 *  `SourceText` input, and files that are not open (imports) are read from disk by the compiler. Programs
 *  (`.hgn`) get every feature, facts files (`.facts`) syntax diagnostics.
 */
final class Features(using db: Database):
  /** The open documents: path to URI as the client spelled it. */
  private val opened = mutable.LinkedHashMap.empty[String, String]

  def isFacts(path: String): Boolean = path.endsWith(".facts")

  /** The URI of a path: the client's own for an open document. */
  def uriOf(path: String): Option[String] = opened.get(path).orElse(Uris.uri(path))

  private def key(path: String) = CompileKey(path)
  private def source(path: String): SourceFile = db(Parse, path).source
  private def offset(path: String, pos: Position): Int = Positions.offset(source(path), pos)
  private def inFile(span: Span, path: String) = span.exists && span.source.path == path
  private def location(span: Span): Option[Location] =
    Option.when(span.exists)(span).flatMap(sp => uriOf(sp.source.path).map(Location(_, Positions.range(sp))))

  // ------------------------------------------------------------------------------------------ documents

  /** Opens a document or replaces its text (full synchronisation). */
  def update(uri: String, text: String): Unit =
    val path = Uris.path(uri)
    opened(path) = uri
    db.set(SourceText, path, text)

  /** Closes a document: from now on the file is read from disk again, like any import. */
  def close(uri: String): Unit =
    val path = Uris.path(uri)
    opened.remove(path)
    db.remove(SourceText, path)

  /** Files changed on disk: those that are not open are read again on their next use. */
  def changedOnDisk(uri: String): Unit =
    val path = Uris.path(uri)
    if !opened.contains(path) then db.remove(SourceText, path)

  // ---------------------------------------------------------------------------------------- diagnostics

  /** Whether a URI is that of an open document. */
  def isOpen(uri: String): Boolean = opened.valuesIterator.contains(uri)

  /** The compiler's diagnostics for a document by file ([[hugin.query.FileDiagnostics]]): its own and those
   *  in the files it imports, each library's read from the queries that named and elaborated it. */
  def fileDiagnostics(path: String): List[FileDiagnostics] =
    try
      if isFacts(path) then List(FileDiagnostics(path, db(Parse, path).diagnostics)).filter(_.diagnostics.nonEmpty)
      else FileDiagnostics.of(key(path))
    catch
      case NonFatal(e) =>
        // a compiler crash must not take the other documents' diagnostics with it
        val crash = HDiagnostic(Severity.Error, None, s"internal compiler error: $e", notes = List("please report this as a bug"))
        List(FileDiagnostics(path, List(crash)))

  /** The compiler's diagnostics for a document, including those in the files it imports. */
  def compilerDiagnostics(path: String): List[HDiagnostic] = fileDiagnostics(path).flatMap(_.diagnostics)

  /** The diagnostics to publish, by URI: every open document (possibly with none) and every imported file
   *  with diagnostics. An open file is reported from its own compilation; a file that is not open, from the
   *  compilations of the documents importing it (the diagnostics of its own queries, shared by them).
   *  Diagnostics without a position belong to the document whose compilation reported them. The bundled
   *  standard library has no URI and is skipped. */
  def diagnostics: Map[String, List[Diagnostic]] =
    val byFile = mutable.LinkedHashMap.empty[String, mutable.ListBuffer[HDiagnostic]]
    for path <- opened.keys do byFile(path) = mutable.ListBuffer.empty
    for path <- opened.keys; f <- fileDiagnostics(path) do
      val file = if f.path == SourceFile.NoSource.path then path else f.path
      if file == path || !opened.contains(file) then byFile.getOrElseUpdate(file, mutable.ListBuffer.empty) ++= f.diagnostics
    (for (file, ds) <- byFile; uri <- uriOf(file) yield uri -> ds.distinct.map(toLsp).toList).toMap

  /** The diagnostics of one document. */
  def diagnosticsOf(uri: String): List[Diagnostic] = diagnostics.getOrElse(uri, Nil)

  /** The range is the primary label's; its message, the notes and the helps form the message; secondary
   *  labels and the meta-level call chain become related information. */
  def toLsp(d: HDiagnostic): Diagnostic =
    val primary = d.labels.find(_.primary).filter(_.span.exists)
    val text = (d.message :: primary.map(_.message).filter(_.nonEmpty).toList) ++
      d.notes.map("note: " + _) ++ d.helps.map("help: " + _)
    val range = primary.map(l => Positions.range(l.span)).getOrElse(Range(Position(0, 0), Position(0, 0)))
    val out = Diagnostic(range, text.mkString("\n"), severity(d.severity), "hugin")
    d.code.foreach(c => out.setCode(c.id))
    if d.code.exists(_.unnecessary) then out.setTags(List(DiagnosticTag.Unnecessary).asJava)
    val secondary =
      for
        l <- d.labels if !l.primary
        loc <- location(l.span)
      yield DiagnosticRelatedInformation(loc, if l.message.nonEmpty then l.message else "related location")
    val frames = d.origin.frames.flatMap(f => location(f.span).map(DiagnosticRelatedInformation(_, f.description)))
    if secondary.nonEmpty || frames.nonEmpty then out.setRelatedInformation((secondary ++ frames).asJava)
    out

  private def severity(s: Severity) = s match
    case Severity.Error => DiagnosticSeverity.Error
    case Severity.Warning => DiagnosticSeverity.Warning
    case Severity.Note => DiagnosticSeverity.Information

  // ----------------------------------------------------------------------------------- position queries

  /** The signature as a Hugin code block, then the compiler's notes (staging, family instances) as
   *  Markdown paragraphs. */
  def hover(uri: String, pos: Position): Option[Hover] =
    val path = Uris.path(uri)
    if isFacts(path) then None
    else
      Ide.hoverInfo(key(path), offset(path, pos)).map { info =>
        val parts = info.signature.map(sig => s"```hugin\n$sig\n```").toList ++ info.notes
        Hover(MarkupContent(MarkupKind.MARKDOWN, parts.mkString("\n\n")))
      }

  /** The declaration of the name at a position; nothing for declarations of the bundled standard library. */
  def definition(uri: String, pos: Position): List[Location] =
    val path = Uris.path(uri)
    if isFacts(path) then Nil else Ide.definition(key(path), offset(path, pos)).flatMap(location).toList

  def references(uri: String, pos: Position, includeDeclaration: Boolean): List[Location] =
    val path = Uris.path(uri)
    if isFacts(path) then Nil
    else
      val off = offset(path, pos)
      val decl = Ide.definition(key(path), off)
      Ide.references(key(path), off).filter(sp => includeDeclaration || !decl.contains(sp)).flatMap(location)

  /** Characters after which clients should ask for completions: module members, labels, directives. */
  val completionTriggers: List[String] = List(".", "{", "%")

  def completion(uri: String, pos: Position): List[CompletionItem] =
    val path = Uris.path(uri)
    if isFacts(path) then Nil
    else
      Ide.completions(key(path), offset(path, pos)).map { c =>
        val item = CompletionItem(c.label)
        item.setKind(completionKind(c.kind))
        item.setDetail(c.detail)
        item
      }

  private def completionKind(kind: String): CompletionItemKind = kind match
    case "directive" => CompletionItemKind.Keyword
    case "variable" | "meta parameter" => CompletionItemKind.Variable
    case "label" => CompletionItemKind.Field
    case "relation" => CompletionItemKind.Function
    case "constructor" => CompletionItemKind.Constructor
    case "struct" => CompletionItemKind.Struct
    case "object type" | "base type" => CompletionItemKind.Class
    case "type definition" => CompletionItemKind.TypeParameter
    case "formula function" => CompletionItemKind.Method
    case "meta definition" => CompletionItemKind.Module
    case _ => CompletionItemKind.Text

  // -------------------------------------------------------------------------------------------- outline

  /** The outline, nested by enclosing definitions (module bodies). */
  def documentSymbols(uri: String): List[DocumentSymbol] =
    val path = Uris.path(uri)
    if isFacts(path) then return Nil
    final class Node(val sym: hugin.query.DocumentSymbol):
      val children = mutable.ListBuffer.empty[Node]
      def extent: Span = children.foldLeft(sym.extent)((sp, c) => sp.to(c.extent))
      def toLsp: DocumentSymbol =
        val out = DocumentSymbol(sym.name, symbolKind(sym.kind), Positions.range(extent), Positions.range(sym.span), sym.kind.describe)
        out.setChildren(children.map(_.toLsp).asJava)
        out
    val roots = mutable.ListBuffer.empty[Node]
    val all = mutable.ListBuffer.empty[Node]
    for s <- Ide.symbols(key(path)) do
      val node = Node(s)
      val parent = s.container.flatMap { c =>
        all
          .filter(n =>
            n.sym.name == c && n.sym.kind == SymKind.MetaDef && n.sym.extent.start <= s.span.start && s.span.end <= n.sym.extent.end
          )
          .minByOption(n => n.sym.extent.end - n.sym.extent.start)
      }
      parent.fold(roots)(_.children) += node
      all += node
    roots.map(_.toLsp).toList

  private def symbolKind(k: SymKind): SymbolKind = k match
    case SymKind.ObjType | SymKind.BaseType => SymbolKind.Class
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
    case SymKind.ObjType | SymKind.TypeDef | SymKind.BaseType => 1
    case SymKind.Struct => 2
    case SymKind.Rel => 3
    case SymKind.Ctor => 4
    case SymKind.FormulaFn => 5
    case SymKind.MetaParam => 6

  /** Semantic tokens from the semantic index: declarations, resolved names and object variables, encoded
   *  relative to the previous token as the protocol requires. */
  def semanticTokens(uri: String): SemanticTokens =
    val path = Uris.path(uri)
    if isFacts(path) then return SemanticTokens(List.empty[Integer].asJava)
    val index = db(Compile, key(path)).index
    val decls = index.symbols.map(s => (s.span, s.name, tokenType(s.kind), 1))
    val uses = index.references.map(r => (r.span, r.sym.name, tokenType(r.sym.kind), 0))
    val vars = index.variables.map(v => (v.span, v.name, 7, 0))
    val tokens = (decls ++ uses ++ vars)
      .filter((sp, name, _, _) => inFile(sp, path) && sp.text == name)
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

  /** Quick fixes for the diagnostics overlapping a range: their suggestions (see
   *  [[hugin.util.diagnostics.Suggestion]]), the first one of each diagnostic preferred. An edit may lie in
   *  another file (a signature); suggestions with edits in the bundled standard library are not offered. */
  def codeActions(uri: String, range: Range): List[CodeAction] =
    val path = Uris.path(uri)
    if isFacts(path) then return Nil
    val src = source(path)
    val (from, to) = (Positions.offset(src, range.getStart), Positions.offset(src, range.getEnd))
    for
      d <- compilerDiagnostics(path)
      sp = d.primarySpan
      if inFile(sp, path) && sp.start <= to && from <= sp.end
      (s, i) <- d.suggestions.zipWithIndex
      edits <- workspaceEdit(s).toList
    yield
      val action = CodeAction(s.message.capitalize)
      action.setKind(CodeActionKind.QuickFix)
      action.setDiagnostics(List(toLsp(d)).asJava)
      action.setEdit(edits)
      action.setIsPreferred(i == 0)
      action

  /** The edits of a suggestion by document, or `None` if one of them lies in a file without a URI. */
  private def workspaceEdit(s: Suggestion): Option[WorkspaceEdit] =
    val byFile = s.edits.groupBy(_.span.source.path).toList
    val targets = byFile.map((path, es) => uriOf(path).map(_ -> es.map(e => TextEdit(Positions.range(e.span), e.replacement)).asJava))
    Option.when(targets.forall(_.isDefined))(WorkspaceEdit(targets.flatten.toMap.asJava))
