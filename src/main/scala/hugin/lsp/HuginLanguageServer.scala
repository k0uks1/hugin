package hugin.lsp

import hugin.query.{Database, SourceText}
import java.io.{InputStream, OutputStream}
import java.util.concurrent.CompletableFuture
import java.util.concurrent.CompletableFuture.completedFuture
import org.eclipse.lsp4j.*
import org.eclipse.lsp4j.jsonrpc.messages.Either as JEither
import org.eclipse.lsp4j.launch.LSPLauncher
import org.eclipse.lsp4j.services.*
import scala.jdk.CollectionConverters.*

/** The Hugin language server. It keeps one query [[Database]]; an opened or changed document (full
 *  synchronisation) sets its `SourceText`, keyed by URI, and the diagnostics of the document are
 *  published. Requests are answered by [[Features]] through the compiler queries, so unchanged documents
 *  are not recompiled.
 *
 *  lsp4j delivers messages one at a time on its listener thread and every handler computes its answer
 *  before returning, so the database is only ever used by one thread.
 */
final class HuginLanguageServer extends LanguageServer with LanguageClientAware:
  private given db: Database = Database()
  private var client: Option[LanguageClient] = None
  private var shutdownRequested = false

  /** Completed with the process exit code when the client sends `exit`. */
  val exited: CompletableFuture[Integer] = CompletableFuture()

  /** The exit code required by the protocol: 0 after a `shutdown` request, 1 otherwise. */
  def exitCode: Int = if shutdownRequested then 0 else 1

  override def connect(c: LanguageClient): Unit = client = Some(c)

  override def initialize(params: InitializeParams): CompletableFuture[InitializeResult] =
    val caps = ServerCapabilities()
    val sync = TextDocumentSyncOptions()
    sync.setOpenClose(true)
    sync.setChange(TextDocumentSyncKind.Full)
    caps.setTextDocumentSync(sync)
    caps.setHoverProvider(true)
    caps.setDefinitionProvider(true)
    caps.setReferencesProvider(true)
    caps.setDocumentSymbolProvider(true)
    val legend = SemanticTokensLegend(Features.tokenTypes.asJava, Features.tokenModifiers.asJava)
    caps.setSemanticTokensProvider(SemanticTokensWithRegistrationOptions(legend, true))
    caps.setCodeActionProvider(CodeActionOptions(List(CodeActionKind.QuickFix).asJava))
    completedFuture(InitializeResult(caps, ServerInfo("hugin")))

  override def shutdown(): CompletableFuture[Object] =
    shutdownRequested = true
    completedFuture(null)

  override def exit(): Unit = exited.complete(exitCode)

  private val documents = Documents()
  private val workspace = Workspace()
  override def getTextDocumentService(): TextDocumentService = documents
  override def getWorkspaceService(): WorkspaceService = workspace

  private def update(uri: String, text: String, version: Int): Unit =
    db.set(SourceText, uri, text)
    publish(uri, Features.diagnostics(uri), Some(version))

  private def publish(uri: String, diags: List[Diagnostic], version: Option[Int]): Unit =
    val params = PublishDiagnosticsParams(uri, diags.asJava)
    version.foreach(v => params.setVersion(v))
    client.foreach(_.publishDiagnostics(params))

  private final class Documents extends TextDocumentService:
    override def didOpen(params: DidOpenTextDocumentParams): Unit =
      val doc = params.getTextDocument
      update(doc.getUri, doc.getText, doc.getVersion)

    override def didChange(params: DidChangeTextDocumentParams): Unit =
      val doc = params.getTextDocument
      params.getContentChanges.asScala.lastOption.foreach(c => update(doc.getUri, c.getText, doc.getVersion))

    override def didClose(params: DidCloseTextDocumentParams): Unit =
      val uri = params.getTextDocument.getUri
      db.remove(SourceText, uri)
      publish(uri, Nil, None)

    override def didSave(params: DidSaveTextDocumentParams): Unit = ()

    override def hover(params: HoverParams): CompletableFuture[Hover] =
      completedFuture(Features.hover(params.getTextDocument.getUri, params.getPosition).orNull)

    override def definition(
        params: DefinitionParams
    ): CompletableFuture[JEither[java.util.List[? <: Location], java.util.List[? <: LocationLink]]] =
      completedFuture(JEither.forLeft(Features.definition(params.getTextDocument.getUri, params.getPosition).asJava))

    override def references(params: ReferenceParams): CompletableFuture[java.util.List[? <: Location]] =
      val include = Option(params.getContext).forall(_.isIncludeDeclaration)
      completedFuture(Features.references(params.getTextDocument.getUri, params.getPosition, include).asJava)

    override def documentSymbol(params: DocumentSymbolParams): CompletableFuture[java.util.List[JEither[SymbolInformation, DocumentSymbol]]] =
      val symbols = Features.documentSymbols(params.getTextDocument.getUri).map(s => JEither.forRight[SymbolInformation, DocumentSymbol](s))
      completedFuture(symbols.asJava)

    override def semanticTokensFull(params: SemanticTokensParams): CompletableFuture[SemanticTokens] =
      completedFuture(Features.semanticTokens(params.getTextDocument.getUri))

    override def codeAction(params: CodeActionParams): CompletableFuture[java.util.List[JEither[Command, CodeAction]]] =
      val actions = Features.codeActions(params.getTextDocument.getUri, params.getRange).map(a => JEither.forRight[Command, CodeAction](a))
      completedFuture(actions.asJava)

  private final class Workspace extends WorkspaceService:
    override def didChangeConfiguration(params: DidChangeConfigurationParams): Unit = ()
    override def didChangeWatchedFiles(params: DidChangeWatchedFilesParams): Unit = ()

object HuginLanguageServer:
  /** Serves the protocol on the given streams until the client sends `exit` or closes the input; returns
   *  the exit code. */
  def serve(in: InputStream, out: OutputStream): Int =
    val server = HuginLanguageServer()
    val launcher = LSPLauncher.createServerLauncher(server, in, out)
    server.connect(launcher.getRemoteProxy)
    val listening = launcher.startListening()
    val closed = CompletableFuture.runAsync(() => scala.util.Try(listening.get()))
    CompletableFuture.anyOf(closed, server.exited).get()
    server.exitCode
