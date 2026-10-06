package hugin.repl

import hugin.compiler.Display
import hugin.util.DiagnosticRenderer
import java.io.{BufferedReader, InputStream, InputStreamReader}
import java.nio.charset.StandardCharsets
import java.nio.file.Path
import org.jline.builtins.Completers.FileNameCompleter
import org.jline.reader.*
import org.jline.reader.impl.DefaultParser
import org.jline.terminal.TerminalBuilder
import scala.jdk.CollectionConverters.*

/** The terminal layer of `hugin repl`: JLine for an interactive terminal, plain line reading otherwise.
 *  Everything else is in [[Session]]. */
object Repl:
  /** The prompt, and the prompt of continuation lines (of an item that has not reached its period). */
  val prompt = "hugin> "
  val continuation = "  ...  "

  /** Runs a session: loads `files` and `facts`, then reads inputs until the end or `:quit`. With `batch`
   *  (or when the console is not a terminal) inputs are read from `in` without prompts; with `echo`, each
   *  input is written to `out` after the prompt, as a transcript. Output goes to `out`, diagnostics to
   *  `err`. Returns false if an input was rejected. */
  def run(
      session: Session,
      files: List[String],
      facts: List[String],
      batch: Boolean,
      echo: Boolean,
      display: Display,
      in: InputStream,
      out: String => Unit,
      err: String => Unit
  ): Boolean =
    val renderer = DiagnosticRenderer(display.color)
    var ok = true
    def show(reply: Reply): Boolean =
      reply.output.foreach(out)
      display.shown(reply.diagnostics).foreach(d => err(renderer.render(d)))
      ok &&= !reply.hasErrors
      !reply.quit
    (files.map(session.load) ++ facts.map(session.loadFacts)).foreach(show)
    if batch || System.console() == null then readAll(session, in, if echo then out else _ => (), show)
    else interactive(session, show, out)
    ok

  /** Reads inputs line by line; an input ends when it is complete (see [[Input]]) or at the end. Each
   *  line goes to `echo` after its prompt. */
  private def readAll(session: Session, in: InputStream, echo: String => Unit, show: Reply => Boolean): Unit =
    val lines = BufferedReader(InputStreamReader(in, StandardCharsets.UTF_8)).lines().iterator().asScala
    var pending: Option[String] = None
    var running = true
    while running && lines.hasNext do
      val line = lines.next()
      echo((if pending.isEmpty then prompt else continuation) + line)
      val text = pending.fold(line)(_ + "\n" + line)
      if Input.isComplete(text) then
        pending = None
        running = show(session.execute(text))
      else pending = Some(text)
    if running then pending.foreach(text => show(session.execute(text)))

  private def interactive(session: Session, show: Reply => Boolean, out: String => Unit): Unit =
    val terminal = TerminalBuilder.builder().system(true).build()
    try
      val reader = LineReaderBuilder
        .builder()
        .terminal(terminal)
        .appName("hugin")
        .parser(ItemParser())
        .completer(SessionCompleter(session))
        .variable(LineReader.HISTORY_FILE, Path.of(System.getProperty("user.home"), ".hugin_history"))
        .variable(LineReader.SECONDARY_PROMPT_PATTERN, continuation)
        .option(LineReader.Option.DISABLE_EVENT_EXPANSION, true)
        .build()
      out("Hugin REPL. Items end with a period; :help lists the commands, :quit ends the session.")
      var running = true
      while running do
        try running = show(session.execute(reader.readLine(prompt)))
        catch
          case _: UserInterruptException => () // Ctrl-C discards the current input
          case _: EndOfFileException => running = false
      reader.getHistory.save()
    finally terminal.close()

  /** Asks JLine for continuation lines while the item is incomplete; splits words for completion. */
  private final class ItemParser extends DefaultParser:
    setQuoteChars(Array('"')) // `'` is part of identifiers

    override def parse(line: String, cursor: Int, context: Parser.ParseContext): ParsedLine =
      if context == Parser.ParseContext.ACCEPT_LINE && !Input.isComplete(line) then throw EOFError(-1, -1, "incomplete item", ".")
      super.parse(line, cursor, context)

  /** Completes with [[Session.complete]]; file names after `:load` and `:facts`. A candidate replaces the
   *  whole word under the cursor (as JLine splits words at blanks), so the part of the word before the
   *  identifier (`roads.` of `roads.pa`) is kept in front of it. */
  private final class SessionCompleter(session: Session) extends Completer:
    private val fileNames = FileNameCompleter()

    def complete(reader: LineReader, line: ParsedLine, candidates: java.util.List[Candidate]): Unit =
      line.words.asScala.take(line.wordIndex).toList match
        case List(":load" | ":facts") => fileNames.complete(reader, line, candidates)
        case _ =>
          val word = line.word.take(line.wordCursor)
          val ident = word.reverseIterator.takeWhile(c => c.isLetterOrDigit || c == '_' || c == '\'').length
          val keep = if word.startsWith(":") then "" else word.dropRight(ident)
          for c <- session.complete(line.line, line.cursor) do
            candidates.add(Candidate(keep + c, c, null, null, null, null, true))
