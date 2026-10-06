package hugin.repl

import hugin.compiler.{Compiler, Settings}
import hugin.query.*
import hugin.syntax.{Lexer, Tok}
import hugin.syntax.Trees.Query as QueryItem
import hugin.util.*
import java.nio.file.{Files, Path}
import org.apache.commons.text.similarity.LevenshteinDistance

/** What the session answers to one input: output lines, diagnostics, and whether to end the session. */
final case class Reply(output: List[String] = Nil, diagnostics: List[Diagnostic] = Nil, quit: Boolean = false):
  def hasErrors: Boolean = diagnostics.exists(_.severity == Severity.Error)

/** A REPL command, for `:help` and completion. */
final case class CommandInfo(name: String, args: String, help: String)

/** An interactive session on top of the query database, independent of any terminal: it takes complete
 *  inputs (see [[Input]]) and returns output and diagnostics.
 *
 *  The session is a program text ([[SessionText]]) set as the input [[SessionText.path]] of the database.
 *  An input becomes a new chunk of a candidate text, which is compiled. If that reports errors, the
 *  previous text is restored and the input is rejected as a whole; otherwise the candidate becomes the
 *  session. Diagnostics are mapped to the chunks they lie in, and only diagnostics the session did not
 *  have before are reported. Queries are answered over the candidate and the facts files, then blanked
 *  out of the session text, so they are answered once.
 */
final class Session(settings: Settings = Settings(), initialBudget: Option[Int] = None, initialStats: Boolean = false):
  private given db: Database = Database()
  private val key = CompileKey(SessionText.path, settings.copy(printAfter = Set.empty, stopAfter = None))

  private var current = SessionText(Vector.empty)

  /** Facts files in load order, with the text they had when they were accepted. */
  private var factFiles = Vector.empty[(String, String)]

  /** The diagnostics of the current session, mapped to chunks; they are not reported again. */
  private var known = Set.empty[Diagnostic]
  private var inputs = 0
  private var budget = initialBudget
  private var stats = initialStats

  restore()

  /** The current session text. */
  def text: String = current.text

  /** The loaded facts files. */
  def facts: List[String] = factFiles.map(_._1).toList

  /** Executes a command, or adds program items (declarations, rules, queries) to the session. */
  def execute(input: String): Reply = Input.status(input) match
    case Input.Status.Empty => Reply()
    case Input.Status.Command => command(input.trim)
    case _ =>
      inputs += 1
      extend(current.chunks :+ Chunk(SourceFile.virtual(s"<input $inputs>", input), file = false), factFiles)

  /** Adds a program file to the session (`:load`). */
  def load(path: String): Reply =
    if current.chunks.exists(c => c.file && c.view.path == path) then error(s"`$path` is already loaded; use :reload to read it again")
    else
      read(path) match
        case None => error(s"no such file `$path`")
        case Some(text) => extend(current.chunks :+ Chunk(SourceFile.virtual(path, text), file = true), factFiles, s"loaded $path")

  /** Loads a facts file for the input relations of the session (`:facts`). */
  def loadFacts(path: String): Reply =
    read(path) match
      case None => error(s"no such facts file `$path`")
      case Some(text) => extend(current.chunks, factFiles.filter(_._1 != path) :+ (path, text), s"loaded facts from $path")

  /** Reads the loaded program and facts files again (`:reload`). */
  def reload(): Reply =
    val files = current.chunks.filter(_.file).map(_.view.path) ++ factFiles.map(_._1)
    val texts = files.flatMap(f => read(f).map(f -> _)).toMap
    files.filterNot(texts.contains) match
      case missing if missing.nonEmpty => error(s"cannot reload: no such file ${missing.map(f => s"`$f`").mkString(", ")}")
      case _ =>
        val chunks = current.chunks.map(c => if c.file then Chunk(SourceFile.virtual(c.view.path, texts(c.view.path)), file = true) else c)
        extend(chunks, factFiles.map((f, _) => (f, texts(f))), s"reloaded ${files.length} file(s)")

  /** Starts an empty session (`:reset`); the budget and statistics settings are kept. */
  def reset(): Reply =
    current = SessionText(Vector.empty)
    factFiles = Vector.empty
    known = Set.empty
    inputs = 0
    restore()
    Reply(List("session cleared"))

  /** Compiles a candidate session. Without errors (and, if there are queries or new facts, with valid
   *  input facts) it becomes the session and its queries are answered; otherwise the session is unchanged. */
  private def extend(chunks: Vector[Chunk], facts: Vector[(String, String)], done: String*): Reply =
    val candidate = SessionText(chunks)
    db.set(SourceText, SessionText.path, candidate.text)
    facts.foreach((f, text) => db.set(SourceText, f, text))
    val compiled = db(Compile, key)
    val diagnostics = compiled.diagnostics.map(candidate.toChunks)
    val fresh = diagnostics.filterNot(known)
    if compiled.hasErrors then
      restore()
      return Reply(diagnostics = fresh)
    val queries = db(Parse, SessionText.path).program.items.collect { case q: QueryItem => q.span }
    val outcome =
      if queries.isEmpty && facts == factFiles then None
      else Some(db(Evaluate, EvaluateKey(key, facts.map(_._1).toList, budget)))
    val factDiagnostics = outcome.toList.flatMap(_.diagnostics)
    if outcome.exists(_.result.isEmpty) then
      restore()
      return Reply(diagnostics = fresh ++ factDiagnostics)
    current = SessionText(chunks.indices.toVector.map { i =>
      val (start, end) = candidate.range(i)
      chunks(i).blank(queries.filter(q => start <= q.start && q.start < end).map(q => (q.start - start, q.end.min(end) - start)))
    })
    factFiles = facts
    known = diagnostics.toSet
    restore()
    val answers =
      for r <- outcome.flatMap(_.result).toList if queries.nonEmpty
      yield r.notice.toList ++ r.answers.flatMap(a => a.query :: a.lines) ++ (if stats then r.statistics else Nil)
    Reply(done.toList ++ answers.flatten, fresh ++ factDiagnostics)

  /** Sets the database inputs to the accepted session. */
  private def restore(): Unit =
    db.set(SourceText, SessionText.path, current.text)
    factFiles.foreach((f, text) => db.set(SourceText, f, text))

  private def read(path: String): Option[String] =
    val p = Path.of(path)
    if Files.isRegularFile(p) then Some(Files.readString(p)) else None

  private def error(message: String, helps: String*): Reply =
    Reply(diagnostics = List(Diagnostic(Severity.Error, None, message, helps = helps.toList)))

  // ------------------------------------------------------------------------------------------ commands

  val commands: List[CommandInfo] = List(
    CommandInfo("load", "<file.hgn>", "add a program file to the session"),
    CommandInfo("reload", "", "read the loaded program and facts files again"),
    CommandInfo("facts", "<file>", "load ground facts for input relations"),
    CommandInfo("reset", "", "start an empty session"),
    CommandInfo("type", "<name>", "describe the symbols with this name"),
    CommandInfo("print", "<phase> [<name>]", "print the session after a phase; with a name, only the items mentioning it"),
    CommandInfo("explain", "<code>", "explain a diagnostic code (e.g. E0401)"),
    CommandInfo("budget", "<n>|off", "round budget for components with %partial relations"),
    CommandInfo("stats", "on|off", "print evaluation statistics after query answers"),
    CommandInfo("help", "", "list the commands"),
    CommandInfo("quit", "", "end the session")
  )

  private def command(line: String): Reply =
    val (name, rest) = line.drop(1).span(!_.isWhitespace)
    val args = rest.trim.split("\\s+").filter(_.nonEmpty).toList
    (name, args) match
      case ("load", List(f)) => load(f)
      case ("reload", Nil) => reload()
      case ("facts", List(f)) => loadFacts(f)
      case ("reset", Nil) => reset()
      case ("type", List(n)) => describe(n)
      case ("print", p :: n) if n.length <= 1 => print(p, n.headOption)
      case ("explain", List(c)) => explain(c)
      case ("budget", List("off")) =>
        budget = None
        Reply(List("round budget: unbounded"))
      case ("budget", List(n)) =>
        n.toIntOption.filter(_ >= 0) match
          case Some(b) =>
            budget = Some(b)
            Reply(List(s"round budget: $b"))
          case None => error(s":budget expects a natural number or `off`, got `$n`")
      case ("stats", List(s @ ("on" | "off"))) =>
        stats = s == "on"
        Reply(List(s"statistics: $s"))
      case ("help", Nil) => Reply(help)
      case ("quit", Nil) => Reply(quit = true)
      case _ =>
        commands.find(_.name == name) match
          case Some(c) => error(s"usage: :${c.name} ${c.args}".trim)
          case None => unknown(name)

  private def unknown(name: String): Reply =
    val distance = LevenshteinDistance.getDefaultInstance
    val similar = commands.map(_.name).filter(c => distance(c, name) <= 2).minByOption(c => distance(c, name))
    error(
      s"unknown command `:$name`",
      similar.map(c => s"did you mean `:$c`?").toList :+ s"the commands are ${commands.map(":" + _.name).mkString(" ")} (see :help)"*
    )

  private def help: List[String] =
    val width = commands.map(c => s":${c.name} ${c.args}".length).max
    List(
      "Enter declarations, rules and directives to add them to the session, and `?- body.` to ask a query.",
      "An item ends with its period; until then, input continues on the next line.",
      ""
    ) ++ commands.map(c => s"  ${s":${c.name} ${c.args}".padTo(width, ' ')}  ${c.help}")

  /** `:type`: the descriptions of the symbols with this name, in source order. */
  private def describe(name: String): Reply =
    val index = db(Compile, key).index
    val descriptions = index.symbols.filter(s => s.name == name && s.span.exists).sortBy(_.span.start).flatMap(index.description).distinct
    if descriptions.isEmpty then error(s"no symbol `$name` in the session") else Reply(descriptions.toList)

  /** `:print`: the session after a phase; with a name, the phase headers and the items mentioning it. */
  private def print(phase: String, name: Option[String]): Reply =
    val phases = Compiler.allPhaseNames :+ "all"
    if !phases.contains(phase) then error(s"unknown phase `$phase`", s"the phases are ${phases.mkString(" ")}")
    else
      val lines = db(Compile, key.copy(settings = key.settings.copy(printAfter = Set(phase)))).printed.flatMap(_.linesIterator)
      Reply(name.fold(lines)(n => Session.mentioning(lines, n)))

  private def explain(code: String): Reply =
    ErrorCodes.lookup(code.toUpperCase) match
      case Some((c, title, text)) => Reply(List(s"$c: $title", "", text))
      case None => error(s"unknown diagnostic code `$code`")

  // ---------------------------------------------------------------------------------------- completion

  /** The names declared in the session, for completion. */
  def names: List[String] = Ide.symbols(key).map(_.name).distinct.sorted

  /** Completion candidates for the word after `before` (the preceding words of the line). Files after
   *  `:load` and `:facts` are left to the terminal layer. */
  def completions(before: List[String]): List[String] = before match
    case Nil => commands.map(":" + _.name) ++ names
    case List(":print") => Compiler.allPhaseNames :+ "all"
    case List(":print", _) | List(":type") => names
    case List(":explain") => ErrorCodes.all.map(_._1)
    case List(":budget") => List("off")
    case List(":stats") => List("on", "off")
    case c :: _ if c.startsWith(":") => Nil
    case _ => names

object Session:
  private val header = "(* ----"

  /** The lines of printed items that mention `name` (also as part of a qualified name `a.name.b`),
   *  together with the phase headers. An item is a line and the indented lines after it. */
  def mentioning(lines: List[String], name: String): List[String] =
    val parts = name.split('.').toList
    val items = lines.foldLeft(Vector.empty[Vector[String]]) { (items, line) =>
      if items.nonEmpty && (line.headOption.exists(_.isWhitespace) || line.startsWith("}")) then items.init :+ (items.last :+ line)
      else items :+ Vector(line)
    }
    items.filter(item => item.head.startsWith(header) || qualifiedNames(item.mkString("\n")).exists(_.containsSlice(parts))).flatten.toList

  /** The names in a printed item; a selection `a.b.c` is one name with parts `a`, `b`, `c`. */
  private def qualifiedNames(text: String): List[List[String]] =
    val tokens = Lexer(SourceFile.virtual("<print>", text), Reporter()).tokenize().toList
    tokens.foldLeft((List.empty[List[String]], false)) { case ((names, selecting), t) =>
      t.kind match
        case Tok.Name if selecting && names.nonEmpty => ((names.head :+ t.text) :: names.tail, false)
        case Tok.Name => (List(t.text) :: names, false)
        case Tok.Select => (names, true)
        case _ => (names, false)
    }._1
