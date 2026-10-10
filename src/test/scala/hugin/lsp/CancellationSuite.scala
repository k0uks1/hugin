package hugin.lsp

import java.util.concurrent.{ExecutionException, TimeUnit}
import org.eclipse.lsp4j.*
import org.eclipse.lsp4j.jsonrpc.ResponseErrorException
import org.eclipse.lsp4j.jsonrpc.messages.ResponseErrorCode
import scala.jdk.CollectionConverters.*

/** The language server works off lsp4j's thread ([[Worker]]): a new edit cancels the work for the old
 *  text, a superseded text's diagnostics are never published, and a document's diagnostics are published
 *  only when they changed. */
class CancellationSuite extends munit.FunSuite:
  private val uri = "untitled:p.hgn"

  private def server(): (HuginLanguageServer, RecordingClient) =
    val s = HuginLanguageServer()
    val c = RecordingClient()
    s.connect(c)
    s.initialize(InitializeParams()).get()
    (s, c)

  private def open(s: HuginLanguageServer, text: String): Unit =
    s.getTextDocumentService.didOpen(DidOpenTextDocumentParams(TextDocumentItem(uri, "hugin", 1, text)))

  private def change(s: HuginLanguageServer, text: String, version: Int = 2): Unit =
    s.getTextDocumentService.didChange(
      DidChangeTextDocumentParams(VersionedTextDocumentIdentifier(uri, version), List(TextDocumentContentChangeEvent(text)).asJava)
    )

  private def idle(s: HuginLanguageServer): Unit = s.idle().get(60, TimeUnit.SECONDS)

  /** The publications received since the last call, as (URI, diagnostics). */
  private def sent(c: RecordingClient): List[(String, List[Diagnostic])] =
    Iterator.continually(c.queue.poll()).takeWhile(_ != null).map(p => (p.getUri, p.getDiagnostics.asScala.toList)).toList

  /** The diagnostics of `text` in a new server: computed from scratch. */
  private def fromScratch(text: String): List[Diagnostic] =
    val (s, c) = server()
    open(s, text)
    idle(s)
    c.published(uri)

  /** The text after `i` keystrokes typing `typed` before the last line of `base`. */
  private def typing(base: String, typed: String, i: Int): String =
    val at = base.lastIndexOf("q X")
    base.take(at) + typed.take(i) + base.drop(at)

  private val base = "p : int -> rel.\n%input p.\nq : int -> rel.\nq X :- p X.\n"

  test("a burst of edits publishes once per document, the final text's diagnostics") {
    val (s, c) = server()
    open(s, base)
    idle(s)
    sent(c)
    val typed = "r : int -> rel.\nr Y :- q Y, s Y.\n"
    // the edits arrive while the worker is busy: each cancels the one before
    s.withDatabase((1 to typed.length).foreach(i => change(s, typing(base, typed, i), i + 1)))
    idle(s)
    val last = typing(base, typed, typed.length)
    val expected = fromScratch(last)
    assertEquals(expected.map(_.getCode.getLeft), List("E0101"))
    assertEquals(sent(c), List(uri -> expected))
  }

  test("an edit that leaves the diagnostics as they were publishes nothing") {
    val (s, c) = server()
    open(s, "p : int -> rel.\np X :- q X.\n")
    idle(s)
    assertEquals(sent(c).map((u, ds) => (u, ds.map(_.getCode.getLeft))), List(uri -> List("E0101")))
    change(s, "p : int -> rel.\np X :- q X.\n(* a comment *)\n")
    idle(s)
    assertEquals(sent(c), Nil)
    // a document without diagnostics is not published either, until it has some
    change(s, "p : int -> rel.\np 1.\n")
    idle(s)
    assertEquals(sent(c), List(uri -> Nil))
    change(s, "p : int -> rel.\np 1.\np 2.\n")
    idle(s)
    assertEquals(sent(c), Nil)
    change(s, "p : int -> rel.\np X :- r X.\n")
    idle(s)
    assertEquals(sent(c).map((u, ds) => (u, ds.map(_.getCode.getLeft))), List(uri -> List("E0101")))
  }

  test("a request cancelled by a later edit answers ContentModified; requests after it see the edit") {
    val (s, _) = server()
    open(s, base)
    idle(s)
    val at = Position(3, 2) // the variable of `q X`
    val (stale, fresh) = s.withDatabase {
      val stale = s.getTextDocumentService.hover(HoverParams(TextDocumentIdentifier(uri), at))
      change(s, base.replace("q X :- p X.", "q Y :- p Y."))
      (stale, s.getTextDocumentService.hover(HoverParams(TextDocumentIdentifier(uri), at)))
    }
    val error = intercept[ExecutionException](stale.get(60, TimeUnit.SECONDS)).getCause
    assertEquals(error.asInstanceOf[ResponseErrorException].getResponseError.getCode, ResponseErrorCode.ContentModified.getValue)
    assert(fresh.get(60, TimeUnit.SECONDS).getContents.getRight.getValue.contains("Y"))
  }

  test("an edit during a compilation cancels it; the final text's diagnostics are published last") {
    val big = (0 until 300).map(i => s"p$i : int -> rel.\np$i X :- p$i X, X < $i.\n").mkString
    val (s, c) = server()
    open(s, big + "q.\n")
    Thread.sleep(20)
    change(s, big + "r : int -> rel.\nr X :- missing X.\n")
    idle(s)
    val published = sent(c)
    assert(published.length <= 2, published.length)
    assertEquals(published.last._2.map(_.getCode.getLeft), List("E0101"))
  }
