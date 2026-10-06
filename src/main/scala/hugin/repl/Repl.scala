package hugin.repl

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
  /** Runs a session: loads `files` and `facts`, then reads inputs until the end or `:quit`. With `batch`
   *  (or when the console is not a terminal) inputs are read from `in` without prompts or echo. Output
   *  goes to `out`, diagnostics to `err`. Returns false if an input was rejected. */
  def run(
      session: Session,
      files: List[String],
      facts: List[String],
      batch: Boolean,
      color: Boolean,
      in: InputStream,
      out: String => Unit,
      err: String => Unit
  ): Boolean =
    val renderer = DiagnosticRenderer(color)
    var ok = true
    def show(reply: Reply): Boolean =
      reply.output.foreach(out)
      reply.diagnostics.foreach(d => err(renderer.render(d)))
      ok &&= !reply.hasErrors
      !reply.quit
    (files.map(session.load) ++ facts.map(session.loadFacts)).foreach(show)
    if batch || System.console() == null then readAll(session, in, show) else interactive(session, show, out)
    ok

  /** Reads inputs line by line; an input ends when it is complete (see [[Input]]) or at the end. */
  private def readAll(session: Session, in: InputStream, show: Reply => Boolean): Unit =
    val lines = BufferedReader(InputStreamReader(in, StandardCharsets.UTF_8)).lines().iterator().asScala
    var pending: Option[String] = None
    var running = true
    while running && lines.hasNext do
      val text = pending.fold(lines.next())(_ + "\n" + lines.next())
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
        .variable(LineReader.SECONDARY_PROMPT_PATTERN, "     | ")
        .option(LineReader.Option.DISABLE_EVENT_EXPANSION, true)
        .build()
      out("Hugin REPL. Items end with a period; :help lists the commands, :quit ends the session.")
      var running = true
      while running do
        try running = show(session.execute(reader.readLine("hugin> ")))
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

  /** Completes commands, phases, diagnostic codes and the names declared in the session; file names after
   *  `:load` and `:facts`. */
  private final class SessionCompleter(session: Session) extends Completer:
    private val fileNames = FileNameCompleter()

    def complete(reader: LineReader, line: ParsedLine, candidates: java.util.List[Candidate]): Unit =
      line.words.asScala.take(line.wordIndex).toList match
        case List(":load" | ":facts") => fileNames.complete(reader, line, candidates)
        case before => session.completions(before).foreach(c => candidates.add(Candidate(c)))
