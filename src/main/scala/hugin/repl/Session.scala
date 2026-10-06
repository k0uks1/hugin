package hugin.repl

import hugin.compiler.{Compiler, Settings, SourceLoader}
import hugin.query.*
import hugin.syntax.{Lexer, Tok}
import hugin.syntax.Trees.Query as QueryItem
import hugin.util.*
import java.nio.file.{Files, Path}
import org.apache.commons.text.similarity.LevenshteinDistance

/** What the session answers to one input: output lines, diagnostics, and whether to end the session. */
final case class Reply(output: List[String] = Nil, diagnostics: List[Diagnostic] = Nil, quit: Boolean = false):
  def hasErrors: Boolean = diagnostics.exists(_.severity == Severity.Error)

/** A REPL command, for `:help` and completion; it can also be called by one of its `aliases`. */
final case class CommandInfo(name: String, args: String, help: String, aliases: List[String] = Nil)

/** An interactive session on top of the query database, independent of any terminal: it takes complete
 *  inputs (see [[Input]]) and returns output and diagnostics.
 *
 *  The session is a program made of several files (a [[hugin.query.Composite]] at [[Session.path]]): its
 *  inputs, each a virtual file `<input N>`, and the loaded program files, each under its own path. So
 *  diagnostics point into the input or file they lie in, with its own lines and columns, and a `%import`
 *  in a loaded file is resolved relative to that file. An input becomes a new part of a candidate
 *  session, which is compiled. If that reports errors, the previous session is restored and the input is
 *  rejected as a whole; otherwise the candidate becomes the session. Only diagnostics the session did not
 *  have before are reported (W0003, an unused definition, is not reported at all: in a session,
 *  definitions are made to be used by later inputs). Queries are answered over the candidate and the facts
 *  files, then left out of the session, so they are answered once.
 *
 *  `:type`, `:kind` and completion ask the position queries of [[hugin.query.Ide]] about a probe: one
 *  more part of the session's program, `<probe>`, removed again afterwards. As an extra item of the
 *  session's program, a probe (like a query) is elaborated on its own over the session's elaborated items,
 *  which are not elaborated again (`docs/INCREMENTALITY.md`, step 10).
 */
final class Session(settings: Settings = Settings(), initialBudget: Option[Int] = None, initialStats: Boolean = false):
  private given db: Database = Database()

  /** The session's query database: every input, probe and `:reload` compiles in it, so the prelude and
   *  imported files are elaborated once for the whole session (for tests). */
  private[repl] def database: Database = db
  private val compileSettings = settings.copy(printAfter = Set.empty, stopAfter = None)
  private val key = CompileKey(Session.path, compileSettings)

  /** Position queries about the probe, in the session's program. */
  private val inProbe = Some(Session.probePath)

  /** The accepted parts of the session, in order. */
  private var current = Vector.empty[Chunk]

  /** Facts files in load order, with the text they had when they were accepted. */
  private var factFiles = Vector.empty[(String, String)]

  /** The texts of the files the session read (loaded program files, facts files, and imported files read
   *  again by `:reload`) as they were accepted; they are the database inputs of these files. */
  private var texts = Map.empty[String, String]

  /** The files (other than the standard library) imported by a session that was accepted, for `:reload`. */
  private var imported = Set.empty[String]

  /** The diagnostics of the current session (see [[Session.identity]]); they are not reported again. */
  private var known = Set.empty[Session.Identity]
  private var inputs = 0
  private var budget = initialBudget
  private var stats = initialStats

  restore()

  /** The current session text: the parts joined by line breaks, without the answered queries. */
  def text: String = current.map(_.text).mkString("\n")

  /** The loaded facts files. */
  def facts: List[String] = factFiles.map(_._1).toList

  /** The files imported (transitively) by the session, in dependency order; the prelude is not listed. */
  def imports: List[String] =
    db(Compile, key).context.unit.libraries.values.filterNot(_.isPrelude).map(_.path).toList

  /** Executes a command, or adds program items (declarations, rules, queries) to the session. */
  def execute(input: String): Reply = Input.status(input) match
    case Input.Status.Empty => Reply()
    case Input.Status.Command => command(input.trim)
    case _ =>
      inputs += 1
      val path = s"<input $inputs>"
      db.set(SourceText, path, input)
      extend(current :+ Chunk(path, input, file = false), Set(path), texts, factFiles)

  /** Adds a program file to the session (`:load`). */
  def load(path: String): Reply =
    if current.exists(c => c.file && c.path == path) then error(s"`$path` is already loaded; use :reload to read it again")
    else
      read(path) match
        case None => error(s"no such file `$path`")
        case Some(text) => extend(current :+ Chunk(path, text, file = true), Set(path), texts + (path -> text), factFiles, s"loaded $path")

  /** Loads a facts file for the input relations of the session (`:facts`). */
  def loadFacts(path: String): Reply =
    read(path) match
      case None => error(s"no such facts file `$path`")
      case Some(text) =>
        extend(current, Set.empty, texts + (path -> text), factFiles.filter(_._1 != path) :+ (path, text), s"loaded facts from $path")

  /** Reads the loaded program and facts files again (`:reload`), and every file the session imported
   *  (transitively); a file that is no longer imported is read when it is imported again. The queries of
   *  the loaded files are answered again. */
  def reload(): Reply =
    val loaded = current.filter(_.file).map(_.path)
    val required = loaded ++ factFiles.map(_._1)
    val files = (required ++ imported.toVector.sorted).distinct
    val read = files.flatMap(f => this.read(f).map(f -> _)).toMap
    required.filterNot(read.contains) match
      case missing if missing.nonEmpty => error(s"cannot reload: no such file ${missing.map(f => s"`$f`").mkString(", ")}")
      case _ =>
        // the imported files as accepted are restored if the reloaded session is rejected
        texts ++= imported.filterNot(texts.contains).flatMap(l => Option.when(db.has(SourceText, l))(l -> db.get(SourceText, l)))
        // a file that is gone is looked for again (and reported missing if it is still imported)
        val gone = imported.filterNot(read.contains)
        gone.foreach(db.remove(SourceText, _))
        val chunks = current.map(c => if c.file then c.copy(text = read(c.path)) else c)
        extend(chunks, loaded.toSet, texts -- gone ++ read, factFiles.map((f, _) => (f, read(f))), s"reloaded ${read.size} file(s)")

  /** Starts an empty session (`:reset`); the budget and statistics settings are kept. */
  def reset(): Reply =
    current = Vector.empty
    factFiles = Vector.empty
    texts = Map.empty
    imported = Set.empty
    known = Set.empty
    inputs = 0
    restore()
    Reply(List("session cleared"))

  /** Compiles a candidate session of `chunks` (answering the queries of the parts in `asked`) with the
   *  file texts `files` and the facts `facts`. Without errors (and, if there are queries or new facts, with
   *  valid input facts) it becomes the session and its queries are answered; otherwise the session is
   *  unchanged. */
  private def extend(
      chunks: Vector[Chunk],
      asked: Set[String],
      files: Map[String, String],
      facts: Vector[(String, String)],
      done: String*
  ): Reply =
    db.set(Composite, Session.path, chunks.map(c => Part(c.path, queries = asked(c.path))))
    files.foreach((f, text) => db.set(SourceText, f, text))
    val compiled = db(Compile, key)
    val diagnostics = compiled.diagnostics.filterNot(Session.silenced)
    val fresh = diagnostics.filterNot(d => known(Session.identity(d)))
    if compiled.hasErrors then
      restore()
      return Reply(diagnostics = fresh)
    val queries = db(ParseProgram, Session.path).program.items.collect { case q: QueryItem => q.span }
    val outcome =
      if queries.isEmpty && facts == factFiles then None
      else Some(db(Evaluate, EvaluateKey(key, facts.map(_._1).toList, budget)))
    val factDiagnostics = outcome.toList.flatMap(_.diagnostics)
    if outcome.exists(_.result.isEmpty) then
      restore()
      return Reply(diagnostics = fresh ++ factDiagnostics)
    current = chunks.map(c => c.blank(queries.filter(_.source.path == c.path).map(q => (q.start, q.end))))
    texts = files
    imported ++= compiled.context.unit.libraries.keys.filterNot(_.startsWith(SourceLoader.StdlibPrefix))
    factFiles = facts
    known = diagnostics.map(Session.identity).toSet
    restore()
    // the query is repeated before its answers when it is not the only one the user just typed
    val answers =
      for r <- outcome.flatMap(_.result).toList if queries.nonEmpty
      yield
        val headers = done.nonEmpty || r.answers.length > 1
        r.notice.toList ++ r.answers.flatMap(a => if headers then a.query :: a.lines else a.lines) ++ (if stats then r.statistics else Nil)
    Reply(done.toList ++ answers.flatten, fresh ++ factDiagnostics)

  /** Sets the database inputs to the accepted session; its queries have been answered. */
  private def restore(): Unit =
    db.set(Composite, Session.path, current.map(c => Part(c.path, queries = false)))
    texts.foreach((f, text) => db.set(SourceText, f, text))

  private def read(path: String): Option[String] =
    try
      val p = Path.of(path)
      if Files.isRegularFile(p) then Some(Files.readString(p)) else None
    catch case _: java.nio.file.InvalidPathException => None

  private def error(message: String, helps: String*): Reply =
    Reply(diagnostics = List(Diagnostic(Severity.Error, None, message, helps = helps.toList)))

  // ------------------------------------------------------------------------------------------ commands

  val commands: List[CommandInfo] = List(
    CommandInfo("load", "<file.hgn>", "add a program file to the session"),
    CommandInfo("reload", "", "read the loaded program and facts files again"),
    CommandInfo("facts", "<file>", "load ground facts for input relations"),
    CommandInfo("reset", "", "start an empty session"),
    CommandInfo("type", "<expr>", "the type of a name, a module path, a meta expression or an object term", List("hover")),
    CommandInfo("kind", "<name>", "what a name (or module path) denotes"),
    CommandInfo("list", "", "show the inputs, files and facts files of the session"),
    CommandInfo("imports", "", "list the files the session imports (transitively)"),
    CommandInfo(
      "print",
      "<phase> [<name>]",
      "print the session after a phase; with a name, only the items mentioning it",
      List("print-after")
    ),
    CommandInfo("explain", "<code>", "explain a diagnostic code (e.g. E0401)"),
    CommandInfo("budget", "<n>|off", "round budget for components with %partial relations"),
    CommandInfo("stats", "on|off", "print evaluation statistics after query answers"),
    CommandInfo("help", "", "list the commands"),
    CommandInfo("quit", "", "end the session")
  )

  /** The command called `name` or by an alias `name`. */
  private def commandNamed(name: String): Option[CommandInfo] = commands.find(c => c.name == name || c.aliases.contains(name))

  private def command(line: String): Reply =
    val (word, rest) = line.drop(1).span(!_.isWhitespace)
    val name = commandNamed(word).fold(word)(_.name)
    val args = rest.trim.split("\\s+").filter(_.nonEmpty).toList
    (name, args) match
      case ("load", List(f)) => load(f)
      case ("reload", Nil) => reload()
      case ("facts", List(f)) => loadFacts(f)
      case ("reset", Nil) => reset()
      case ("type", _ :: _) => typeOf(rest.trim)
      case ("kind", List(n)) => kindOf(n)
      case ("list", Nil) => list
      case ("imports", Nil) => Reply(imports.headOption.fold(List("(* the session imports no files *)"))(_ => imports))
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
        commandNamed(name) match
          case Some(c) => error(s"usage: :$word ${c.args}".trim)
          case None => unknown(name)

  private def unknown(name: String): Reply =
    val distance = LevenshteinDistance.getDefaultInstance
    val similar = commands.flatMap(c => c.name :: c.aliases).filter(c => distance(c, name) <= 2).minByOption(c => distance(c, name))
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
    ) ++ commands.map { c =>
      val aliases = if c.aliases.isEmpty then "" else c.aliases.map(":" + _).mkString(" (also ", ", ", ")")
      s"  ${s":${c.name} ${c.args}".padTo(width, ' ')}  ${c.help}$aliases"
    }

  /** Sets up a probe: `text` as one more part of the session's program, [[Session.probePath]]. Offsets of
   *  position queries about the probe (`in = inProbe`) are offsets into `text`. The session is restored by
   *  [[probing]]. */
  private def probe(text: String): Unit =
    db.set(SourceText, Session.probePath, text)
    db.set(Composite, Session.path, current.map(c => Part(c.path, queries = false)) :+ Part(Session.probePath))

  /** Runs `body`, which sets up probes, and restores the session afterwards. */
  private def probing[T](body: => T): T =
    try body
    finally restore()

  /** The new errors of compiling a probe whose text is `prefix`, `expr` and a period, with their spans
   *  moved into `expr` as entered (`<input>`). */
  private def probeErrors(prefix: String, expr: String): List[Diagnostic] =
    probe(prefix + expr + ".")
    val view = SourceFile.virtual("<input>", expr)
    def move(span: Span): Span =
      if span.source.path != Session.probePath then span
      else
        val start = (span.start - prefix.length).max(0).min(expr.length)
        Span(view, start, (span.end - prefix.length).max(start).min(expr.length))
    db(Compile, key).diagnostics
      .filter(_.severity == Severity.Error)
      .filterNot(d => known(Session.identity(d)))
      .map(d =>
        d.copy(
          labels = d.labels.map(l => l.copy(span = move(l.span))),
          origin = Origin(d.origin.frames.map(f => f.copy(span = move(f.span))))
        )
      )

  /** `:type`: for a name or module path, its description as hover shows it (with the instantiated type of
   *  a member of a module); for an object term, its object type; for another meta expression, its meta
   *  type. Each is asked by compiling a probe item: `?- V = term.` and `it = expr.`. */
  private def typeOf(expr: String): Reply = probing:
    val metaPrefix = s"${Session.probeName} = "
    val errors = probeErrors(metaPrefix, expr)
    val meta =
      if errors.nonEmpty then Left(errors)
      else if Session.isPath(expr) then Right(Ide.hover(key, metaPrefix.length + expr.length - 1, inProbe))
      else Right(Ide.hover(key, 1, inProbe).map(_.stripPrefix(s"meta definition ${Session.probeName} : ")).map(t => s"$expr : $t"))
    val objPrefix = s"?- ${Session.probeVar} = "
    def obj =
      if probeErrors(objPrefix, expr).nonEmpty then None
      else Ide.hover(key, 4, inProbe).map(_.stripPrefix(s"variable ${Session.probeVar} : ")).map(t => s"$expr : $t")
    meta match
      case Left(errors) => Reply(diagnostics = errors)
      case Right(Some(described)) if Session.isPath(expr) => Reply(List(described))
      case Right(metaType) =>
        obj.orElse(metaType) match
          case Some(t) => Reply(List(t))
          case None => error(s"no type for `$expr`")

  /** `:kind`: what a name denotes (an object type, a relation, a constructor, a meta definition, ...). */
  private def kindOf(name: String): Reply = probing:
    if !Session.isPath(name) then error(s":kind expects a name or a module path, got `$name`")
    else
      val prefix = s"${Session.probeName} = "
      probeErrors(prefix, name) match
        case Nil =>
          Ide.symbolAt(key, prefix.length + name.length - 1, inProbe) match
            case Some(s) => Reply(List(s"$name : ${s.kind.describe}"))
            case None => error(s"no symbol `$name` in the session")
        case errors => Reply(diagnostics = errors)

  /** `:list`: the accepted inputs (without the queries, which were answered), loaded files and facts files. */
  private def list: Reply =
    val chunks = current.flatMap { c =>
      if c.file then List(s"(* loaded ${c.path} *)")
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
    ErrorCodes.explain(code) match
      case Some(text) => Reply(text.linesIterator.toList)
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
    else
      probing:
        probe(before + " .")
        Ide.completions(key, before.length, inProbe).map(_.label)

  /** Candidates for a command word, or its argument after the words `previous`. */
  private def commandCompletions(previous: List[String]): List[String] = previous match
    case Nil => commands.flatMap(c => c.name :: c.aliases).map(":" + _)
    case command :: args if commandNamed(command.drop(1)).exists(_.name != command.drop(1)) =>
      commandCompletions(s":${commandNamed(command.drop(1)).get.name}" :: args)
    case List(":print") => Compiler.allPhaseNames :+ "all"
    case List(":print", _) | List(":type") | List(":kind") => names
    case List(":explain") => ErrorCodes.all.map(_._1)
    case List(":budget") => List("off")
    case List(":stats") => List("on", "off")
    case _ => Nil

  /** The top-level names of the session (and the prelude), for the arguments of commands. */
  private def names: List[String] = probing:
    probe("")
    Ide.completions(key, 0, inProbe).map(_.label).distinct.sorted

object Session:
  /** The name of the session program, made of the parts of the session ([[hugin.query.Composite]]). */
  val path = "<repl>"

  /** The name of the extra part of the session's program that is a probe. */
  val probePath = "<probe>"

  private val header = "(* ----"

  /** What identifies a diagnostic across compilations: the source files of a session are parsed again
   *  when their text is set again, so spans are compared by path and offsets. */
  private type Identity = (Severity, Option[String], String, List[(String, Int, Int)])
  private def identity(d: Diagnostic): Identity =
    (d.severity, d.code, d.message, d.labels.map(l => (l.span.source.path, l.span.start, l.span.end)))

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
