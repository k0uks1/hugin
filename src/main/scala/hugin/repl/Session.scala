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
 *  have before are reported (W0003, an unused definition, is not reported at all: in a session,
 *  definitions are made to be used by later inputs). Queries are answered over the candidate and the facts
 *  files, then blanked out of the session text, so they are answered once.
 *
 *  `:type`, `:kind` and completion ask the position queries of [[hugin.query.Ide]] about a probe: a
 *  candidate session text with one more chunk, which is never accepted.
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
    val diagnostics = compiled.diagnostics.filterNot(Session.silenced).map(candidate.toChunks)
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
    // the query is repeated before its answers when it is not the only one the user just typed
    val answers =
      for r <- outcome.flatMap(_.result).toList if queries.nonEmpty
      yield
        val headers = done.nonEmpty || r.answers.length > 1
        r.notice.toList ++ r.answers.flatMap(a => if headers then a.query :: a.lines else a.lines) ++ (if stats then r.statistics else Nil)
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
    CommandInfo("type", "<expr>", "the type of a name, a module path, a meta expression or an object term"),
    CommandInfo("kind", "<name>", "what a name (or module path) denotes"),
    CommandInfo("list", "", "show the inputs, files and facts files of the session"),
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
      case ("type", _ :: _) => typeOf(rest.trim)
      case ("kind", List(n)) => kindOf(n)
      case ("list", Nil) => list
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

  /** Runs `f` on a probe: the session text with `text` as one more chunk. `f` gets the offset of the probe
   *  in the session text; the database inputs are restored afterwards. */
  private def probe[A](text: String)(f: Int => A): A =
    val candidate = SessionText(current.chunks :+ Chunk(SourceFile.virtual("<probe>", text), file = false))
    db.set(SourceText, SessionText.path, candidate.text)
    try f(candidate.offsets.last)
    finally restore()

  /** The new errors of compiling a probe whose text is `prefix`, `expr` and a period, with their spans
   *  moved into `expr` as entered (`<input>`). */
  private def probeErrors(prefix: String, expr: String): List[Diagnostic] =
    val view = SourceFile.virtual("<input>", expr)
    val candidate = SessionText(current.chunks :+ Chunk(SourceFile.virtual("<probe>", prefix + expr + "."), file = false))
    def move(span: Span): Span =
      val mapped = candidate.toChunk(span)
      if mapped.source.path != "<probe>" then mapped
      else
        val start = (mapped.start - prefix.length).max(0).min(expr.length)
        Span(view, start, (mapped.end - prefix.length).max(start).min(expr.length))
    db(Compile, key).diagnostics
      .filter(_.severity == Severity.Error)
      .map(d =>
        d.copy(
          labels = d.labels.map(l => l.copy(span = move(l.span))),
          origin = Origin(d.origin.frames.map(f => f.copy(span = move(f.span))))
        )
      )
      .filterNot(known)

  /** `:type`: for a name or module path, its description as hover shows it (with the instantiated type of
   *  a member of a module); for an object term, its object type; for another meta expression, its meta
   *  type. Each is asked by compiling a probe item: `?- V = term.` and `it = expr.`. */
  private def typeOf(expr: String): Reply =
    val metaPrefix = s"${Session.probeName} = "
    val meta = probe(metaPrefix + expr + ".") { offset =>
      val errors = probeErrors(metaPrefix, expr)
      if errors.nonEmpty then Left(errors)
      else if Session.isPath(expr) then Right(Ide.hover(key, offset + metaPrefix.length + expr.length - 1))
      else Right(Ide.hover(key, offset + 1).map(_.stripPrefix(s"meta definition ${Session.probeName} : ")).map(t => s"$expr : $t"))
    }
    val objPrefix = s"?- ${Session.probeVar} = "
    def obj = probe(objPrefix + expr + ".") { offset =>
      if probeErrors(objPrefix, expr).nonEmpty then None
      else Ide.hover(key, offset + 4).map(_.stripPrefix(s"variable ${Session.probeVar} : ")).map(t => s"$expr : $t")
    }
    meta match
      case Left(errors) => Reply(diagnostics = errors)
      case Right(Some(described)) if Session.isPath(expr) => Reply(List(described))
      case Right(metaType) =>
        obj.orElse(metaType) match
          case Some(t) => Reply(List(t))
          case None => error(s"no type for `$expr`")

  /** `:kind`: what a name denotes (an object type, a relation, a constructor, a meta definition, ...). */
  private def kindOf(name: String): Reply =
    if !Session.isPath(name) then error(s":kind expects a name or a module path, got `$name`")
    else
      val prefix = s"${Session.probeName} = "
      probe(prefix + name + ".") { offset =>
        probeErrors(prefix, name) match
          case Nil =>
            Ide.symbolAt(key, offset + prefix.length + name.length - 1) match
              case Some(s) => Reply(List(s"$name : ${s.kind.describe}"))
              case None => error(s"no symbol `$name` in the session")
          case errors => Reply(diagnostics = errors)
      }

  /** `:list`: the accepted inputs (without the queries, which were answered), loaded files and facts files. */
  private def list: Reply =
    val chunks = current.chunks.flatMap { c =>
      if c.file then List(s"(* loaded ${c.view.path} *)")
      else c.text.linesIterator.map(_.stripTrailing).toList.dropWhile(_.isEmpty).reverse.dropWhile(_.isEmpty).reverse
    }
    val facts = factFiles.map((f, _) => s"(* facts from $f *)")
    if chunks.isEmpty && facts.isEmpty then Reply(List("(* the session is empty *)")) else Reply((chunks ++ facts).toList)

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

  /** Completion candidates for the identifier before `cursor` in `line` (the input typed so far, possibly
   *  several lines): commands and their arguments for a command line, otherwise
   *  [[hugin.query.Ide.completions]] at the cursor of a probe (the input up to the cursor, terminated).
   *  Files after `:load` and `:facts` are left to the terminal layer. */
  def complete(line: String, cursor: Int): List[String] =
    val before = line.take(cursor)
    if Input.isCommand(before) then
      val words = before.trim.split("\\s+").toList
      val previous = if before.last.isWhitespace then words else words.init
      commandCompletions(previous).filter(_.startsWith(if before.last.isWhitespace then "" else words.last))
    else probe(before + " .")(offset => Ide.completions(key, offset + before.length).map(_.label))

  /** Candidates for a command word, or its argument after the words `previous`. */
  private def commandCompletions(previous: List[String]): List[String] = previous match
    case Nil => commands.map(":" + _.name)
    case List(":print") => Compiler.allPhaseNames :+ "all"
    case List(":print", _) | List(":type") | List(":kind") => names
    case List(":explain") => ErrorCodes.all.map(_._1)
    case List(":budget") => List("off")
    case List(":stats") => List("on", "off")
    case _ => Nil

  /** The top-level names of the session (and the prelude), for the arguments of commands. */
  private def names: List[String] = probe("")(offset => Ide.completions(key, offset)).map(_.label).distinct.sorted

object Session:
  private val header = "(* ----"

  /** The names of the probe items of `:type`, chosen not to clash with names of the session. */
  private val probeName = "it'repl"
  private val probeVar = "It'repl"

  /** Diagnostics that the session does not report: W0003 (unused definition). */
  private def silenced(d: Diagnostic): Boolean = d.code.contains("W0003")

  /** Whether a text is a name or a module path `a.b.c`. */
  private def isPath(text: String): Boolean = text.split('.').forall(_.matches("[A-Za-z_][A-Za-z0-9_']*"))

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
