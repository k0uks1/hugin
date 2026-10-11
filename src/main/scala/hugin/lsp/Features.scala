package hugin.lsp

import hugin.compiler.SymKind
import hugin.ide.{CandidateKind, Fix, FixKind, Target}
import hugin.query.{CompileKey, Compile, Database, FileDiagnostics, Parse, SourceText}
import hugin.util.{Diagnostic as HDiagnostic, Severity, SourceFile, Span}
import hugin.util.diagnostics.Code
import org.eclipse.lsp4j.*
import scala.collection.mutable
import scala.jdk.CollectionConverters.*

/** The language features of the server in terms of the protocol: URIs, 0-based UTF-16 positions and
 *  lsp4j's data types. What the features answer is decided by the protocol-independent editor layer
 *  [[hugin.ide]] (shared with the browser build and the CLI); every method converts the position to an
 *  offset, calls it, and encodes the result.
 *
 *  Documents are keyed in the database by their path (see [[Uris]]); an open document's text is its
 *  `SourceText` input, and files that are not open (imports) are read from disk by the compiler. Programs
 *  (`.hgn`) get every feature, facts files (`.facts`) syntax diagnostics.
 */
final class Features(using db: Database):
  /** The meta-level features (hover, inlay hints, holes, interactive code actions), and their settings. */
  val meta: MetaFeatures = MetaFeatures()

  /** The open documents: path to URI as the client spelled it. */
  private val opened = mutable.LinkedHashMap.empty[String, String]

  def isFacts(path: String): Boolean = hugin.ide.Files.isFacts(path)

  /** The URI of a path: the client's own for an open document. */
  def uriOf(path: String): Option[String] = opened.get(path).orElse(Uris.uri(path))

  private def key(path: String) = CompileKey(path)
  private def source(path: String): SourceFile = db(Parse, path).source
  private def offset(path: String, pos: Position): Int = Positions.offset(source(path), pos)
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

  /** The compiler's diagnostics for a document by file ([[hugin.ide.Diagnostics]]): its own and those in
   *  the files it imports, each library's read from the queries that named and elaborated it. */
  def fileDiagnostics(path: String): List[FileDiagnostics] = hugin.ide.Diagnostics.of(key(path))

  /** The compiler's diagnostics for a document, including those in the files it imports. */
  def compilerDiagnostics(path: String): List[HDiagnostic] = fileDiagnostics(path).flatMap(_.diagnostics)

  /** The diagnostics to publish, by URI: every open document (possibly with none) and every imported file
   *  with diagnostics. An open file is reported from its own compilation; a file that is not open, from the
   *  compilations of the documents importing it (the diagnostics of its own queries, shared by them).
   *  Diagnostics without a position belong to the document whose compilation reported them. The bundled
   *  standard library has no URI and is skipped. */
  def diagnostics: Map[String, List[Diagnostic]] =
    // each with the document whose compilation reported it (for the goals of typed holes)
    val byFile = mutable.LinkedHashMap.empty[String, mutable.ListBuffer[(String, HDiagnostic)]]
    for path <- opened.keys do byFile(path) = mutable.ListBuffer.empty
    for path <- opened.keys; f <- fileDiagnostics(path) do
      val file = if f.path == SourceFile.NoSource.path then path else f.path
      if file == path || !opened.contains(file) then byFile.getOrElseUpdate(file, mutable.ListBuffer.empty) ++= f.diagnostics.map(path -> _)
    (for (file, ds) <- byFile; uri <- uriOf(file) yield uri -> ds.distinctBy(_._2).map((p, d) => toLsp(d, p)).toList).toMap

  /** The diagnostics of one document. */
  def diagnosticsOf(uri: String): List[Diagnostic] = diagnostics.getOrElse(uri, Nil)

  /** The range is the primary label's; its message, the notes and the helps form the message; secondary
   *  labels and the meta-level call chain become related information. */
  def toLsp(d: HDiagnostic): Diagnostic = toLsp(d, "")

  /** As [[toLsp]]; the goal of a typed hole (E0924) is the diagnostic's `data`, from the compilation of
   *  the document at `path`. */
  def toLsp(d: HDiagnostic, path: String): Diagnostic =
    val out = plain(d)
    if path.nonEmpty then meta.goalData(path, d).foreach(out.setData)
    out

  private def plain(d: HDiagnostic): Diagnostic =
    val primary = d.labels.find(_.primary).filter(_.span.exists)
    val text = (d.message :: primary.map(_.message).filter(_.nonEmpty).toList) ++
      d.notes.map("note: " + _) ++ d.helps.map("help: " + _)
    val range = primary.map(l => Positions.range(l.span)).getOrElse(Range(Position(0, 0), Position(0, 0)))
    val out = Diagnostic(range, text.mkString("\n"), severity(d.severity), "hugin")
    out.setCode(d.code.id)
    out.setCodeDescription(DiagnosticCodeDescription(Features.explanationLink(d.code)))
    if d.code.unnecessary then out.setTags(List(DiagnosticTag.Unnecessary).asJava)
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

  /** The signature as a Hugin code block, then the notes as Markdown paragraphs ([[hugin.ide.Hover]]). */
  def hover(uri: String, pos: Position): Option[Hover] =
    val path = Uris.path(uri)
    hugin.ide.Hover.at(key(path), offset(path, pos)).map { h =>
      val parts = h.signature.map(sig => s"```hugin\n$sig\n```").toList ++ h.notes
      Hover(MarkupContent(MarkupKind.MARKDOWN, parts.mkString("\n\n")))
    }

  /** The declaration of the name at a position; nothing for declarations of the bundled standard library. */
  def definition(uri: String, pos: Position): List[Location] =
    val path = Uris.path(uri)
    hugin.ide.Navigation.definition(key(path), offset(path, pos)).toList.flatMap {
      case Target.InFile(span) => location(span)
      case Target.Library(_, _) => None
    }

  def references(uri: String, pos: Position, includeDeclaration: Boolean): List[Location] =
    val path = Uris.path(uri)
    hugin.ide.Navigation.references(key(path), offset(path, pos), includeDeclaration).flatMap(location)

  /** Characters after which clients should ask for completions ([[hugin.ide.Completion.triggers]]). */
  val completionTriggers: List[String] = hugin.ide.Completion.triggers

  /** The candidates of [[hugin.ide.Completion]]; where they are ranked, those that fit come first
   *  (`sortText`) and are preselected. */
  def completion(uri: String, pos: Position): List[CompletionItem] =
    val path = Uris.path(uri)
    val cs = hugin.ide.Completion.at(key(path), offset(path, pos))
    cs.items.map { c =>
      val item = CompletionItem(c.label)
      item.setKind(completionKind(c.kind))
      item.setDetail(c.detail)
      if cs.ranked then item.setSortText((if c.fits then "0" else "1") + c.label)
      if c.fits then item.setPreselect(true)
      item
    }

  private def completionKind(kind: CandidateKind): CompletionItemKind = kind match
    case CandidateKind.Directive => CompletionItemKind.Keyword
    case CandidateKind.Variable | CandidateKind.MetaParameter => CompletionItemKind.Variable
    case CandidateKind.Label => CompletionItemKind.Field
    case CandidateKind.Relation => CompletionItemKind.Function
    case CandidateKind.Constructor => CompletionItemKind.Constructor
    case CandidateKind.Struct => CompletionItemKind.Struct
    case CandidateKind.ObjectType | CandidateKind.BaseType => CompletionItemKind.Class
    case CandidateKind.TypeDefinition => CompletionItemKind.TypeParameter
    case CandidateKind.FormulaFunction => CompletionItemKind.Method
    case CandidateKind.MetaDefinition => CompletionItemKind.Module
    case CandidateKind.Other => CompletionItemKind.Text

  // -------------------------------------------------------------------------------------------- outline

  /** The outline ([[hugin.ide.Outline]]), nested by enclosing definitions (module bodies). */
  def documentSymbols(uri: String): List[DocumentSymbol] =
    def toLsp(n: hugin.ide.Outline.Node): DocumentSymbol =
      val s = n.symbol
      val out = DocumentSymbol(s.name, symbolKind(s.kind), Positions.range(n.extent), Positions.range(s.span), s.kind.describe)
      out.setChildren(n.children.map(toLsp).asJava)
      out
    hugin.ide.Outline.of(key(Uris.path(uri))).map(toLsp)

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

  /** Token types and modifiers of the semantic tokens legend ([[Tokens]]). */
  val tokenTypes: List[String] = Tokens.types
  val tokenModifiers: List[String] = Tokens.modifiers

  def semanticTokens(uri: String): SemanticTokens =
    val path = Uris.path(uri)
    if isFacts(path) then SemanticTokens(List.empty[Integer].asJava)
    else Tokens.of(db(Compile, key(path)).index, source(path), path)

  // ------------------------------------------------------------------------------------------ expansion

  /** The staged result of the meta code at a position (command `hugin.expansion`). */
  def expansion(uri: String, pos: Position): Option[String] =
    val path = Uris.path(uri)
    hugin.ide.Expansions.at(key(path), offset(path, pos))

  def codeLenses(uri: String): List[CodeLens] = meta.codeLenses(uri, Uris.path(uri))

  // ---------------------------------------------------------------------------------------- inlay hints

  def inlayHints(uri: String, range: Range): List[InlayHint] = meta.inlayHints(Uris.path(uri), range)

  // --------------------------------------------------------------------------------------- code actions

  /** The fixes of [[hugin.ide.Fixes]] for a range: quick fixes from the diagnostics' suggestions and the
   *  code actions of interactive development. A fix with an edit in a file without a URI is not offered. */
  def codeActions(uri: String, range: Range): List[CodeAction] =
    val path = Uris.path(uri)
    val src = source(path)
    val (from, to) = (Positions.offset(src, range.getStart), Positions.offset(src, range.getEnd))
    hugin.ide.Fixes.at(key(path), path, from, to).flatMap(f => codeAction(f, uri, path))

  private def codeAction(f: Fix, uri: String, path: String): Option[CodeAction] =
    workspaceEdit(f, uri, path).map { edit =>
      val action = CodeAction(f.title)
      action.setKind(f.kind match
        case FixKind.QuickFix => CodeActionKind.QuickFix
        case FixKind.Rewrite => CodeActionKind.RefactorRewrite
      )
      // a fix of a diagnostic says whether it is preferred; the others leave it to the client
      f.diagnostic.foreach { d =>
        action.setDiagnostics(List(toLsp(d)).asJava)
        action.setIsPreferred(f.preferred)
      }
      action.setEdit(edit)
      action
    }

  /** The edits of a fix by document (the request's URI for its own file), or `None` if one of them lies in
   *  a file without a URI. */
  private def workspaceEdit(f: Fix, uri: String, path: String): Option[WorkspaceEdit] =
    val byFile = f.edits.groupBy(_.span.source.path).toList
    val targets = byFile.map { (p, es) =>
      (if p == path then Some(uri) else uriOf(p)).map(_ -> es.map(e => TextEdit(Positions.range(e.span), e.text)).asJava)
    }
    Option.when(targets.forall(_.isDefined))(WorkspaceEdit(targets.flatten.toMap.asJava))

object Features:
  /** The link of a code's explanation (LSP `codeDescription`): its page in the error index of the published
   *  language reference. */
  def explanationLink(c: Code): String = c.explanationUrl
