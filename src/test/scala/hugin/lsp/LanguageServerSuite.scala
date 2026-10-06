package hugin.lsp

import java.io.{PipedInputStream, PipedOutputStream}
import java.nio.file.{Files, Path}
import java.util.concurrent.{CompletableFuture, LinkedBlockingQueue, TimeUnit}
import org.eclipse.lsp4j.*
import org.eclipse.lsp4j.launch.LSPLauncher
import org.eclipse.lsp4j.services.LanguageClient
import scala.collection.mutable
import scala.jdk.CollectionConverters.*

/** A client that records the published diagnostics. */
class RecordingClient extends LanguageClient:
  val published: mutable.Map[String, List[Diagnostic]] = mutable.LinkedHashMap.empty
  val queue = LinkedBlockingQueue[PublishDiagnosticsParams]()
  override def publishDiagnostics(p: PublishDiagnosticsParams): Unit =
    published(p.getUri) = p.getDiagnostics.asScala.toList
    queue.put(p)
  override def telemetryEvent(o: Object): Unit = ()
  override def showMessage(p: MessageParams): Unit = ()
  override def showMessageRequest(p: ShowMessageRequestParams): CompletableFuture[MessageActionItem] =
    CompletableFuture.completedFuture(null)
  override def logMessage(p: MessageParams): Unit = ()

/** The server's request handlers, called directly on in-memory documents. */
class LanguageServerSuite extends munit.FunSuite:
  private val program =
    """graph : mod = { node : type, edge : node -> node -> rel }.
      |tc (g : graph) = {
      |  path : g.node -> g.node -> rel.
      |  path X Y :- g.edge X Y.
      |  path X Z :- g.edge X Y, path Y Z.
      |}.
      |city : type. berlin : city. paris : city.
      |road : city -> city -> rel.
      |%input road.
      |roads = tc { node = city, edge = road }.
      |%output roads.path.
      |n : int -> rel.
      |""".stripMargin

  private val uri = "untitled:p.hgn"

  /** The LSP position of the `n`-th occurrence of `needle` in `text`, plus `shift` characters. */
  private def pos(needle: String, shift: Int = 0, n: Int = 0, text: String = program): Position =
    val off = Iterator.iterate(text.indexOf(needle))(i => text.indexOf(needle, i + 1)).drop(n).next() + shift
    Positions.position(hugin.util.SourceFile.virtual("", text), off)

  private def server(): (HuginLanguageServer, RecordingClient) =
    val s = HuginLanguageServer()
    val c = RecordingClient()
    s.connect(c)
    s.initialize(InitializeParams()).get()
    (s, c)

  private def open(s: HuginLanguageServer, uri: String, text: String): Unit =
    s.getTextDocumentService.didOpen(DidOpenTextDocumentParams(TextDocumentItem(uri, "hugin", 1, text)))

  private def change(s: HuginLanguageServer, uri: String, text: String): Unit =
    s.getTextDocumentService.didChange(
      DidChangeTextDocumentParams(VersionedTextDocumentIdentifier(uri, 2), List(TextDocumentContentChangeEvent(text)).asJava)
    )

  private def doc(uri: String) = TextDocumentIdentifier(uri)

  test("diagnostics are published on open and change, and cleared on close") {
    val (s, c) = server()
    open(s, uri, "p : int -> rel.\np X :- q X.\n")
    val d = c.published(uri).loneElement
    assertEquals(d.getCode.getLeft, "E0101")
    assertEquals(d.getSeverity, DiagnosticSeverity.Error)
    assertEquals(d.getRange.getStart, Position(1, 7))
    assertEquals(d.getRange.getEnd, Position(1, 8))
    assert(d.getMessage.startsWith("unresolved name `q`"), d.getMessage)
    change(s, uri, "p : int -> rel.\np 1.\n")
    assertEquals(c.published(uri), Nil)
    change(s, uri, "p : int -> rel.\np X :- q X.\n")
    s.getTextDocumentService.didClose(DidCloseTextDocumentParams(doc(uri)))
    assertEquals(c.published(uri), Nil)
  }

  test("secondary labels become related information; notes and helps join the message") {
    val (s, c) = server()
    open(s, uri, "p : rel.\np : rel.\n")
    val d = c.published(uri).loneElement
    assertEquals(d.getCode.getLeft, "E0102")
    val related = d.getRelatedInformation.asScala.toList.loneElement
    assertEquals(related.getLocation.getUri, uri)
    assertEquals(related.getLocation.getRange.getStart, Position(0, 0))
  }

  test("singleton variables are tagged as unnecessary") {
    val (s, c) = server()
    open(s, uri, "e : int -> int -> rel.\n%input e.\nsrc : int -> rel.\nsrc X :- e X Y.\n")
    val d = c.published(uri).loneElement
    assertEquals(d.getSeverity, DiagnosticSeverity.Warning)
    assertEquals(d.getTags.asScala.toList, List(DiagnosticTag.Unnecessary))
  }

  test("hover shows the type, instantiated at a module path") {
    val (s, _) = server()
    open(s, uri, program)
    val hover = s.getTextDocumentService.hover(HoverParams(doc(uri), pos("roads.path", "roads.".length))).get()
    assertEquals(hover.getContents.getRight.getValue, "```hugin\nrelation roads.path : city -> city -> rel\n```")
    assertEquals(s.getTextDocumentService.hover(HoverParams(doc(uri), Position(30, 0))).get(), null)
  }

  test("definition and references, through module paths") {
    val (s, _) = server()
    open(s, uri, program)
    val defs = s.getTextDocumentService.definition(DefinitionParams(doc(uri), pos("roads.path", "roads.".length))).get().getLeft.asScala
    assertEquals(defs.map(l => (l.getUri, l.getRange.getStart)).toList, List((uri, pos("path :"))))
    val refs = s.getTextDocumentService.references(ReferenceParams(doc(uri), pos("road :"), ReferenceContext(true))).get().asScala
    assertEquals(refs.map(_.getRange.getStart).toList, List(pos("road :"), pos("road."), pos("road }")))
    val uses = s.getTextDocumentService.references(ReferenceParams(doc(uri), pos("road :"), ReferenceContext(false))).get().asScala
    assertEquals(uses.size, 2)
  }

  test("definitions in the bundled prelude are not returned") {
    val (s, _) = server()
    open(s, uri, program)
    val defs = s.getTextDocumentService.definition(DefinitionParams(doc(uri), pos("int"))).get().getLeft.asScala
    assertEquals(defs.toList, Nil)
  }

  test("document symbols are nested by module bodies") {
    val (s, _) = server()
    open(s, uri, program)
    val symbols = s.getTextDocumentService.documentSymbol(DocumentSymbolParams(doc(uri))).get().asScala.map(_.getRight).toList
    val tc = symbols.find(_.getName == "tc").get
    assertEquals(tc.getKind, SymbolKind.Module)
    assertEquals(tc.getChildren.asScala.map(c => (c.getName, c.getKind)).toList, List(("path", SymbolKind.Function)))
    assertEquals(tc.getSelectionRange.getStart, pos("tc"))
    assertEquals(tc.getRange.getStart, pos("tc"))
    assert(symbols.exists(d => d.getName == "road" && d.getKind == SymbolKind.Function))
    assert(symbols.exists(d => d.getName == "berlin" && d.getKind == SymbolKind.Constructor))
  }

  test("completion of directives, module members and names in scope") {
    val (s, _) = server()
    val text = program + "q : city -> rel.\nq X :- roads.pa X X, ro X X.\n%out\n"
    open(s, uri, text)
    def complete(needle: String) =
      s.getTextDocumentService.completion(CompletionParams(doc(uri), pos(needle, needle.length, text = text))).get().getLeft.asScala.toList
    val directive = complete("%out").loneElement
    assertEquals((directive.getLabel, directive.getKind), ("output", CompletionItemKind.Keyword))
    assertEquals(complete("roads.pa").map(c => (c.getLabel, c.getKind)), List(("path", CompletionItemKind.Function)))
    assertEquals(complete(", ro").map(_.getLabel), List("road", "roads"))
  }

  test("a facts file gets syntax diagnostics only") {
    val (s, c) = server()
    open(s, "untitled:f.facts", "road berlin")
    assertEquals(c.published("untitled:f.facts").loneElement.getCode.getLeft, "E0001")
  }

  test("imported files: diagnostics, definitions and edits") {
    val dir = Files.createTempDirectory("hugin-lsp")
    try
      val lib = dir.resolve("geo.hgn")
      Files.writeString(lib, "place : type.\nhere : place.\nbad X :- nothing X.\n")
      val main = dir.resolve("main.hgn")
      val mainText = "g = %import \"geo\".\nat : g.place -> rel.\nat g.here.\n"
      val (s, c) = server()
      val mainUri = main.toUri.toString
      val libUri = lib.toUri.toString
      open(s, mainUri, mainText)
      // the error in the (unopened) imported file is published for that file
      assert(c.published(libUri).nonEmpty, c.published)
      val defs = s.getTextDocumentService.definition(DefinitionParams(doc(mainUri), pos("here", text = mainText))).get().getLeft.asScala
      assertEquals(defs.map(l => (l.getUri, l.getRange.getStart)).toList, List((libUri, Position(1, 0))))
      // fixing the file in the editor clears them, and the importer sees the edit
      open(s, libUri, "place : type.\nhere : place.\n")
      assertEquals(c.published(libUri), Nil)
      assertEquals(c.published(mainUri), Nil)
      change(s, libUri, "place : type.\n")
      assert(c.published(mainUri).nonEmpty)
    finally
      Files.walk(dir).sorted(java.util.Comparator.reverseOrder()).forEach(Files.delete)
  }

  test("code actions: replace a singleton variable with `_`") {
    val (s, _) = server()
    val text = "e : int -> int -> rel.\n%input e.\nsrc : int -> rel.\nsrc X :- e X Y.\n"
    open(s, uri, text)
    val y = pos("Y", text = text)
    val actions = s.getTextDocumentService.codeAction(CodeActionParams(doc(uri), Range(y, y), CodeActionContext(Nil.asJava))).get().asScala
    val fix = actions.map(_.getRight).find(_.getIsPreferred).get
    val edit = fix.getEdit.getChanges.get(uri).asScala.loneElement
    assertEquals((edit.getNewText, edit.getRange.getStart), ("_", y))
  }

  test("the server speaks the protocol over streams") {
    val toServer = PipedOutputStream()
    val serverIn = PipedInputStream(toServer)
    val toClient = PipedOutputStream()
    val clientIn = PipedInputStream(toClient)
    val exit = CompletableFuture[Int]()
    val serving = Thread((() => { exit.complete(HuginLanguageServer.serve(serverIn, toClient)); () }): Runnable, "test-lsp-server")
    serving.setDaemon(true)
    serving.start()
    val client = RecordingClient()
    val launcher = LSPLauncher.createClientLauncher(client, clientIn, toServer)
    launcher.startListening()
    val remote = launcher.getRemoteProxy
    val caps = remote.initialize(InitializeParams()).get(10, TimeUnit.SECONDS).getCapabilities
    assert(caps.getHoverProvider.getLeft)
    remote.initialized(InitializedParams())
    remote.getTextDocumentService.didOpen(DidOpenTextDocumentParams(TextDocumentItem(uri, "hugin", 1, "p : rel.\np :- q.\n")))
    val published = client.queue.poll(10, TimeUnit.SECONDS)
    assertEquals(published.getDiagnostics.asScala.map(_.getCode.getLeft).toList, List("E0101"))
    val hover = remote.getTextDocumentService.hover(HoverParams(doc(uri), Position(0, 0))).get(10, TimeUnit.SECONDS)
    assert(hover.getContents.getRight.getValue.contains("p : rel"), hover)
    remote.shutdown().get(10, TimeUnit.SECONDS)
    remote.exit()
    assertEquals(exit.get(10, TimeUnit.SECONDS), 0)
    toServer.close()
    toClient.close()
  }

  extension [A](xs: Iterable[A])
    private def loneElement: A =
      assertEquals(xs.size, 1, xs)
      xs.head
