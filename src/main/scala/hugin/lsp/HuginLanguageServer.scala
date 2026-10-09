package hugin.lsp

import hugin.query.Database
import java.io.{InputStream, OutputStream}
import java.util.concurrent.CompletableFuture
import java.util.concurrent.CompletableFuture.completedFuture
import org.eclipse.lsp4j.*
import org.eclipse.lsp4j.jsonrpc.messages.Either as JEither
import org.eclipse.lsp4j.launch.LSPLauncher
import org.eclipse.lsp4j.services.*
import scala.jdk.CollectionConverters.*

/** The Hugin language server. It keeps one query [[hugin.query.Database]]; an opened or changed document (full
 *  synchronisation) sets its `SourceText`, and diagnostics are published per file: those of every open
 *  document again (an edit can affect the documents importing the edited one), and those of the files they
 *  import (from the queries of those files) when they changed, and cleared when they disappeared. Requests
 *  are answered by [[Features]] through the compiler queries, so unchanged documents are not recompiled.
 *
 *  lsp4j delivers messages one at a time on its listener thread and every handler computes its answer
 *  before returning, so the database is only ever used by one thread.
 */
final class HuginLanguageServer extends LanguageServer with LanguageClientAware:
  private given db: Database = Database()
  private var client: Option[LanguageClient] = None
  private var shutdownRequested = false

  /** The features, for tests. */
  val features: Features = Features()

  /** The diagnostics the client currently has, by URI (only non-empty lists): to clear them when they
   *  disappear, and to publish those of a file that is not open only when they changed. */
  private var published = Map.empty[String, List[Diagnostic]]

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
    caps.setCompletionProvider(CompletionOptions(false, features.completionTriggers.asJava))
    val legend = SemanticTokensLegend(features.tokenTypes.asJava, features.tokenModifiers.asJava)
    caps.setSemanticTokensProvider(SemanticTokensWithRegistrationOptions(legend, true))
    caps.setCodeActionProvider(CodeActionOptions(List(CodeActionKind.QuickFix, CodeActionKind.RefactorRewrite).asJava))
    caps.setInlayHintProvider(true)
    caps.setCodeLensProvider(CodeLensOptions(false))
    caps.setExecuteCommandProvider(ExecuteCommandOptions(List(MetaFeatures.ExpansionCommand).asJava))
    features.meta.hintSettings = HintSettings.from(params.getInitializationOptions, features.meta.hintSettings)
    completedFuture(InitializeResult(caps, ServerInfo("hugin")))

  override def shutdown(): CompletableFuture[Object] =
    shutdownRequested = true
    completedFuture(null)

  override def exit(): Unit = exited.complete(exitCode)

  private val documents = Documents()
  private val workspace = Workspace()
  override def getTextDocumentService(): TextDocumentService = documents
  override def getWorkspaceService(): WorkspaceService = workspace

  /** Publishes the diagnostics of all open documents and those of the files they import that changed, and
   *  clears those of files that no longer have any. */
  private def publish(): Unit =
    val now = features.diagnostics
    for uri <- published.keySet -- now.keySet do send(uri, Nil)
    for (uri, diags) <- now if features.isOpen(uri) || published.getOrElse(uri, Nil) != diags do send(uri, diags)
    published = now.filter(_._2.nonEmpty)

  private def send(uri: String, diags: List[Diagnostic]): Unit =
    client.foreach(_.publishDiagnostics(PublishDiagnosticsParams(uri, diags.asJava)))

  private final class Documents extends TextDocumentService:
    override def didOpen(params: DidOpenTextDocumentParams): Unit =
      val doc = params.getTextDocument
      features.update(doc.getUri, doc.getText)
      publish()

    override def didChange(params: DidChangeTextDocumentParams): Unit =
      // with full synchronisation, the last change is the whole text
      params.getContentChanges.asScala.lastOption.foreach(c => features.update(params.getTextDocument.getUri, c.getText))
      publish()

    override def didClose(params: DidCloseTextDocumentParams): Unit =
      val uri = params.getTextDocument.getUri
      features.close(uri)
      send(uri, Nil)
      published -= uri
      publish()

    override def didSave(params: DidSaveTextDocumentParams): Unit = ()

    override def hover(params: HoverParams): CompletableFuture[Hover] =
      completedFuture(features.hover(params.getTextDocument.getUri, params.getPosition).orNull)

    override def completion(params: CompletionParams): CompletableFuture[JEither[java.util.List[CompletionItem], CompletionList]] =
      completedFuture(JEither.forLeft(features.completion(params.getTextDocument.getUri, params.getPosition).asJava))

    override def definition(
        params: DefinitionParams
    ): CompletableFuture[JEither[java.util.List[? <: Location], java.util.List[? <: LocationLink]]] =
      completedFuture(JEither.forLeft(features.definition(params.getTextDocument.getUri, params.getPosition).asJava))

    override def references(params: ReferenceParams): CompletableFuture[java.util.List[? <: Location]] =
      val include = Option(params.getContext).forall(_.isIncludeDeclaration)
      completedFuture(features.references(params.getTextDocument.getUri, params.getPosition, include).asJava)

    override def documentSymbol(params: DocumentSymbolParams)
        : CompletableFuture[java.util.List[JEither[SymbolInformation, DocumentSymbol]]] =
      val symbols = features.documentSymbols(params.getTextDocument.getUri).map(s => JEither.forRight[SymbolInformation, DocumentSymbol](s))
      completedFuture(symbols.asJava)

    override def semanticTokensFull(params: SemanticTokensParams): CompletableFuture[SemanticTokens] =
      completedFuture(features.semanticTokens(params.getTextDocument.getUri))

    override def codeLens(params: CodeLensParams): CompletableFuture[java.util.List[? <: CodeLens]] =
      completedFuture(features.codeLenses(params.getTextDocument.getUri).asJava)

    override def inlayHint(params: InlayHintParams): CompletableFuture[java.util.List[InlayHint]] =
      completedFuture(features.inlayHints(params.getTextDocument.getUri, params.getRange).asJava)

    override def codeAction(params: CodeActionParams): CompletableFuture[java.util.List[JEither[Command, CodeAction]]] =
      val actions = features.codeActions(params.getTextDocument.getUri, params.getRange).map(a => JEither.forRight[Command, CodeAction](a))
      completedFuture(actions.asJava)

  private final class Workspace extends WorkspaceService:
    /** The settings under `hugin` (`inlayHints`); hints are asked for again by the client. */
    override def didChangeConfiguration(params: DidChangeConfigurationParams): Unit =
      features.meta.hintSettings = HintSettings.from(params.getSettings, features.meta.hintSettings)

    /** `hugin.expansion` ([[MetaFeatures.ExpansionCommand]]): the expansion at a position, or null. */
    override def executeCommand(params: ExecuteCommandParams): CompletableFuture[Object] =
      val result =
        if params.getCommand != MetaFeatures.ExpansionCommand then None
        else
          MetaFeatures.positionArgs(Option(params.getArguments).fold(Nil)(_.asScala.toList)).flatMap((uri, pos) =>
            features.expansion(uri, pos)
          )
      completedFuture(result.orNull)

    override def didChangeWatchedFiles(params: DidChangeWatchedFilesParams): Unit =
      params.getChanges.asScala.foreach(e => features.changedOnDisk(e.getUri))
      publish()

object HuginLanguageServer:
  /** Serves the protocol on the given streams until the client sends `exit` or closes the input; returns
   *  the exit code. */
  def serve(in: InputStream, out: OutputStream): Int =
    val server = HuginLanguageServer()
    val launcher = LSPLauncher.createServerLauncher(server, in, out)
    server.connect(launcher.getRemoteProxy)
    val listening = launcher.startListening()
    // wait for whichever comes first on a thread of our own: blocking inside the common fork-join pool can
    // run the other wait on the waiting thread itself and never return
    val closed = CompletableFuture[Unit]()
    val watcher = Thread((() => { scala.util.Try(listening.get()); closed.complete(()); () }): Runnable, "hugin-lsp-input")
    watcher.setDaemon(true)
    watcher.start()
    CompletableFuture.anyOf(closed, server.exited).get()
    server.exitCode
