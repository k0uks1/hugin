package hugin.lsp

import com.google.gson.{GsonBuilder, JsonArray, JsonElement, JsonObject, JsonParser}
import java.io.{ByteArrayOutputStream, InputStream, OutputStream, PipedInputStream, PipedOutputStream}
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}
import java.util.concurrent.{CompletableFuture, LinkedBlockingQueue, TimeUnit}
import scala.jdk.CollectionConverters.*

/** Recorded protocol transcripts, replayed against the server over streams (like an editor talks to
 *  `hugin lsp`).
 *
 *  - `tests/lsp/X.in`: the client's messages, one JSON-RPC message per line (blank lines and lines
 *    starting with `//` are skipped). Each is sent with its `Content-Length` header; after a request the
 *    replay waits for its response, so the server's notifications (published diagnostics) land between
 *    the requests in a fixed order. The last messages should be `shutdown` and `exit`; the server must then
 *    exit with code 0.
 *  - `tests/lsp/X.check`: the transcript, normalized: `-->` client messages compact, `<--` server messages
 *    pretty-printed, keys sorted.
 *
 *  Set `HUGIN_UPDATE_CHECKS=1` to (re)write the check files.
 */
class TranscriptSuite extends munit.FunSuite:
  private val update = sys.env.get("HUGIN_UPDATE_CHECKS").contains("1")
  private val timeoutSeconds = 30L

  private val pretty = GsonBuilder().setPrettyPrinting().disableHtmlEscaping().create()
  private val compact = GsonBuilder().disableHtmlEscaping().create()

  /** The JSON with the keys of every object sorted, so that transcripts do not depend on field order. */
  private def sorted(e: JsonElement): JsonElement = e match
    case o: JsonObject =>
      val out = JsonObject()
      o.keySet.asScala.toList.sorted.foreach(k => out.add(k, sorted(o.get(k))))
      out
    case a: JsonArray =>
      val out = JsonArray()
      a.asScala.foreach(x => out.add(sorted(x)))
      out
    case other => other

  private def send(out: OutputStream, message: String): Unit =
    val body = message.getBytes(UTF_8)
    out.write(s"Content-Length: ${body.length}\r\n\r\n".getBytes(UTF_8))
    out.write(body)
    out.flush()

  /** Reads one framed message; `None` at the end of the stream. */
  private def receive(in: InputStream): Option[String] =
    def line(): Option[String] =
      val buf = ByteArrayOutputStream()
      var c = in.read()
      while c != -1 && c != '\n' do
        if c != '\r' then buf.write(c)
        c = in.read()
      if c == -1 && buf.size == 0 then None else Some(buf.toString(UTF_8))
    var length = -1
    var header = line()
    while header.exists(_.nonEmpty) do
      header.foreach(h => if h.toLowerCase.startsWith("content-length:") then length = h.drop("content-length:".length).trim.toInt)
      header = line()
    if header.isEmpty || length < 0 then None
    else Some(String(in.readNBytes(length), UTF_8))

  private def replay(script: Path): String =
    val toServer = PipedOutputStream()
    val serverIn = PipedInputStream(toServer, 1 << 16)
    val fromServer = PipedOutputStream()
    val clientIn = PipedInputStream(fromServer, 1 << 16)
    val exit = CompletableFuture[Int]()
    val serving = Thread((() => { exit.complete(HuginLanguageServer.serve(serverIn, fromServer)); () }): Runnable, "transcript-server")
    serving.setDaemon(true)
    serving.start()
    val received = LinkedBlockingQueue[JsonObject]()
    val reader = Thread(
      (
          () =>
            Iterator.continually(scala.util.Try(receive(clientIn)).toOption.flatten).takeWhile(_.isDefined).flatten.foreach { m =>
              received.put(JsonParser.parseString(m).getAsJsonObject)
            }
      ): Runnable,
      "transcript-reader"
    )
    reader.setDaemon(true)
    reader.start()
    val transcript = StringBuilder()
    def record(m: JsonObject): Unit = transcript ++= "<-- " ++= pretty.toJson(sorted(m)) += '\n'
    try
      val messages = Files.readAllLines(script).asScala.map(_.trim).filter(l => l.nonEmpty && !l.startsWith("//"))
      for text <- messages do
        val message = JsonParser.parseString(text).getAsJsonObject
        transcript ++= "--> " ++= compact.toJson(sorted(message)) += '\n'
        send(toServer, compact.toJson(message))
        if message.has("id") && message.has("method") then
          // a request: everything the server sends up to its response
          val id = message.get("id")
          var answered = false
          while !answered do
            val m = Option(received.poll(timeoutSeconds, TimeUnit.SECONDS)).getOrElse(fail(s"no response to request $id\n$transcript"))
            record(m)
            answered = m.has("id") && m.get("id") == id && !m.has("method")
        else if message.get("method").getAsString == "exit" then
          assertEquals(exit.get(timeoutSeconds, TimeUnit.SECONDS), 0, "exit code after `shutdown` and `exit`")
      Iterator.continually(received.poll()).takeWhile(_ != null).foreach(record)
      transcript.toString
    finally
      toServer.close()
      fromServer.close()

  private val dir = Path.of("tests", "lsp")
  private val scripts =
    if Files.isDirectory(dir) then Files.list(dir).iterator().asScala.filter(_.toString.endsWith(".in")).toList.sortBy(_.toString)
    else Nil

  test("there are transcripts") {
    assert(scripts.nonEmpty)
  }

  for script <- scripts do
    test(s"lsp/${script.getFileName}") {
      val actual = replay(script)
      val check = Path.of(script.toString.stripSuffix(".in") + ".check")
      if update || !Files.exists(check) then
        Files.writeString(check, actual)
        if !update then fail(s"no check file for $script; wrote ${check.getFileName}")
      else assertNoDiff(actual, Files.readString(check), s"transcript of $script differs from ${check.getFileName}")
    }
