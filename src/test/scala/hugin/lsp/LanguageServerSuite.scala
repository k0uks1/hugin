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
    """graph : Type = { node : type, edge : node -> node -> rel }.
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
    // the code links to its page in the error index of the published reference (reference/site-url.txt)
    val site = Files.readString(Path.of("reference/site-url.txt")).trim
    assertEquals(d.getCodeDescription.getHref, s"${site.stripSuffix("/")}/errors/E0101.html")
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

  test("a file with syntax errors: one diagnostic each; hover, definition, completion and symbols work elsewhere") {
    val (s, c) = server()
    // a broken rule body, an unclosed parenthesis in a module member, a missing period
    val text = program.replace("paris : city.", "paris : city") +
      "far : city -> rel.\nfar X :- roads.path berlin X, .\nnear : city -> rel.\nnear X :- road (berlin X.\n" +
      "q : city -> rel.\nq X :- roads.pa X X, ro X X.\n"
    open(s, uri, text)
    val diagnostics = c.published(uri).map(d => (d.getCode.getLeft, d.getRange.getStart.getLine))
    // (and the field `pa` that the completion below is asked for)
    assertEquals(diagnostics, List(("E0001", 6), ("E0001", 13), ("E0005", 15), ("E0906", 17)))
    // the missing period comes with its fix
    val fix = s.getTextDocumentService
      .codeAction(CodeActionParams(doc(uri), c.published(uri).head.getRange, CodeActionContext(c.published(uri).take(1).asJava)))
      .get().asScala.map(_.getRight).loneElement
    assertEquals(fix.getEdit.getChanges.get(uri).asScala.map(_.getNewText).toList, List("."))
    val hover = s.getTextDocumentService.hover(HoverParams(doc(uri), pos("roads.path", "roads.".length, text = text))).get()
    assertEquals(hover.getContents.getRight.getValue, "```hugin\nrelation roads.path : city -> city -> rel\n```")
    // (not in the broken items, which are not elaborated)
    val defs = s.getTextDocumentService.definition(DefinitionParams(doc(uri), pos("road }", 0, text = text))).get().getLeft.asScala
    assertEquals(defs.map(_.getRange.getStart).toList, List(pos("road :", text = text)))
    def complete(needle: String) =
      s.getTextDocumentService.completion(CompletionParams(doc(uri), pos(needle, needle.length, text = text))).get().getLeft.asScala.toList
    assertEquals(complete("roads.pa").map(_.getLabel), List("path"))
    assertEquals(complete(", ro").map(_.getLabel), List("road", "roads"))
    val symbols = s.getTextDocumentService.documentSymbol(DocumentSymbolParams(doc(uri))).get().asScala.map(_.getRight.getName).toList
    assert(Set("tc", "roads", "far", "near", "q").subsetOf(symbols.toSet), symbols)
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

  test("diagnostics are published per file: an error in an imported file on its URI, cleared once fixed") {
    val dir = Files.createTempDirectory("hugin-lsp")
    try
      val lib = dir.resolve("geo.hgn")
      Files.writeString(lib, "place : type.\nhere : place.\nbad X :- nothing X.\n")
      val main = dir.resolve("main.hgn")
      val other = dir.resolve("other.hgn")
      val (s, c) = server()
      val (mainUri, otherUri, libUri) = (main.toUri.toString, other.toUri.toString, lib.toUri.toString)
      open(s, mainUri, "g = %import \"geo\".\nat : g.place -> rel.\nat g.here.\n")
      val errors = c.published(libUri)
      assertEquals(errors.map(_.getCode.getLeft), List("E0101"))
      assertEquals(errors.map(_.getRange.getStart), List(Position(2, 0)))
      assertEquals(c.published(mainUri), Nil)
      def sent(uri: String) =
        val all = Iterator.continually(c.queue.poll()).takeWhile(_ != null).toList
        all.filter(_.getUri == uri).map(_.getDiagnostics.asScala.toList)
      sent(libUri)
      // editing the importer (or opening another importer) does not publish the library's unchanged diagnostics again
      change(s, mainUri, "g = %import \"geo\".\nat : g.place -> rel.\nat g.here.\nat X :- at X.\n")
      open(s, otherUri, "h = %import \"geo\".\n")
      assertEquals(sent(libUri), Nil)
      assertEquals(c.published(libUri), errors)
      // fixed on disk: the library's diagnostics are cleared, on its URI
      Files.writeString(lib, "place : type.\nhere : place.\n")
      s.getWorkspaceService.didChangeWatchedFiles(DidChangeWatchedFilesParams(List(FileEvent(libUri, FileChangeType.Changed)).asJava))
      assertEquals(sent(libUri), List(Nil))
      assertEquals(c.published(mainUri), Nil)
      // broken again: published again
      Files.writeString(lib, "place : type.\nhere : place.\nhere : place.\n")
      s.getWorkspaceService.didChangeWatchedFiles(DidChangeWatchedFilesParams(List(FileEvent(libUri, FileChangeType.Changed)).asJava))
      assertEquals(sent(libUri).map(_.length), List(1))
      // once no open document imports it, its diagnostics are cleared
      change(s, mainUri, "at : int -> rel.\n")
      s.getTextDocumentService.didClose(DidCloseTextDocumentParams(doc(otherUri)))
      assertEquals(c.published(libUri), Nil)
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

  test("hover shows the staging of meta values and the instances of families") {
    val (s, _) = server()
    val text = "k : int = 6 * 7.\nat_k : int -> rel.\nat_k X :- X = k.\nnums : list int -> rel.\nnums (cons 1 nil).\n"
    open(s, uri, text)
    def hover(needle: String, shift: Int) =
      s.getTextDocumentService.hover(HoverParams(doc(uri), pos(needle, shift, text = text))).get().getContents.getRight.getValue
    assertEquals(
      hover("X = k", 4),
      "```hugin\nmeta definition k : int\n```\n\npersisted: the compile-time value `42` is embedded as a literal"
    )
    assertEquals(hover("cons 1", 0), "```hugin\nconstructor cons A : A -> list A -> list A\n```\n\ninstance: `cons[int]`")
  }

  private def actions(s: HuginLanguageServer, at: Position): List[CodeAction] =
    s.getTextDocumentService.codeAction(CodeActionParams(doc(uri), Range(at, at), CodeActionContext(Nil.asJava))).get().asScala.map(
      _.getRight
    ).toList

  test("code actions: missing labels, in the order the compiler suggests them") {
    val (s, _) = server()
    val text = "p : (a : int) -> (b : int) -> rel.\n%input p.\nq : int -> rel.\nq X :- p { a = X }.\n"
    open(s, uri, text)
    val fixes = actions(s, pos("{ a", text = text))
    assertEquals(
      fixes.map(a => (a.getTitle, a.getIsPreferred.booleanValue)),
      List(("Add the missing labels", true), ("Ignore the missing labels with `..`", false))
    )
    val edit = fixes.head.getEdit.getChanges.get(uri).asScala.loneElement
    assertEquals(
      (edit.getNewText, edit.getRange.getStart, edit.getRange.getEnd),
      (", b = _", pos(" }", text = text), pos(" }", text = text))
    )
    assertEquals(fixes.head.getDiagnostics.asScala.loneElement.getCode.getLeft, "E0301")
  }

  test("code actions: add `%complete edge` to the signature, away from the diagnostic") {
    val (s, _) = server()
    val text =
      """g : Type = { node : type, edge : node -> node -> rel }.
        |iso (x : g) = {
        |  lonely : x.node -> rel.
        |  lonely N :- x.edge N _, not x.edge _ N.
        |}.
        |""".stripMargin
    open(s, uri, text)
    val fix = actions(s, pos("x.edge _ N", text = text)).loneElement
    assertEquals(fix.getTitle, "Add `%complete edge`")
    val edit = fix.getEdit.getChanges.get(uri).asScala.loneElement
    assertEquals((edit.getNewText, edit.getRange.getStart), (", %complete edge", pos(" }.", text = text)))
  }

  test("code actions: nothing for a diagnostic without suggestions, or away from diagnostics") {
    val (s, _) = server()
    val text = "p : int -> rel.\np X :- zzz X.\nr : rel.\n"
    open(s, uri, text)
    assertEquals(actions(s, pos("zzz", text = text)), Nil)
    assertEquals(actions(s, pos("r : rel", text = text)), Nil)
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
