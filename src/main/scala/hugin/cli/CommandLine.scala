package hugin.cli

import hugin.compiler.{Compiler, Display, Settings}
import scopt.{OEffect, OParser}

/** What the user asked for. */
enum Command:
  case Run(file: String)
  case Check(file: String)
  case Phases

  /** The explanation of a code, or with `list` the inventory of all codes. */
  case Explain(code: String, list: Boolean = false)

  /** A position query (`hover`, `definition`, `references`) or a file query (`symbols`, `diagnostics`);
   *  positions are 1-based `line:column`. */
  case Query(file: String, request: String, position: Option[(Int, Int)])

  /** An interactive session, starting with the given program files; `batch` reads it from stdin without
   *  prompts, `echo` writes each input line after its prompt (a transcript). */
  case Repl(files: List[String], batch: Boolean, echo: Boolean = false)

  /** The language server, speaking LSP over stdin and stdout. */
  case Lsp
  case Help

/** Options of `hugin run` that do not influence compilation. */
final case class RunOptions(
    /** Files of ground facts for input relations. */
    facts: List[String] = Nil,
    /** Print evaluation statistics to stderr. */
    stats: Boolean = false,
    /** Print every relation, including fact constructors and demand relations. */
    allRelations: Boolean = false
)

final case class Options(
    command: Command,
    settings: Settings,
    run: RunOptions,
    display: Display = Display(),
    /** Use the new meta level (docs/REDESIGN.md, Phase B) instead of the compiler pipeline: `check`
     *  elaborates, `run` prints the elaborated and staged program. Hidden while it is being developed. */
    newMeta: Boolean = false
)

/** Command-line parsing with scopt. `parse` is pure: scopt's effects are interpreted here, so nothing is
 *  printed and the process is never terminated. */
object CommandLine:
  private val builder = OParser.builder[Options]

  private val parser: OParser[Unit, Options] =
    import builder.*
    val knownPhases = Compiler.allPhaseNames.toSet + "all"
    def phases(ps: Seq[String]) =
      ps.find(p => !knownPhases(p)) match
        case Some(p) => failure(s"unknown phase `$p`; see `hugin phases`")
        case None => success
    OParser.sequence(
      programName("hugin"),
      head("hugin", "reference implementation of the Hugin language"),
      help("help").abbr("h").text("show this help"),
      cmd("run")
        .text("compile and evaluate; print output relations and query answers")
        .action((_, o) => o.copy(command = Command.Run("")))
        .children(arg[String]("<file.hgn>").action((f, o) => o.copy(command = Command.Run(f)))),
      cmd("check")
        .text("compile only and report diagnostics")
        .action((_, o) => o.copy(command = Command.Check("")))
        .children(arg[String]("<file.hgn>").action((f, o) => o.copy(command = Command.Check(f)))),
      cmd("phases")
        .text("list the compiler phases")
        .action((_, o) => o.copy(command = Command.Phases)),
      cmd("explain")
        .text("explain a diagnostic code (e.g. E0401); --list lists all codes by phase")
        .action((_, o) => o.copy(command = Command.Explain("")))
        .children(
          opt[Unit]("list")
            .text("list every diagnostic code by phase")
            .action((_, o) => o.copy(command = Command.Explain("", list = true))),
          arg[String]("<code>")
            .optional()
            .action((c, o) =>
              o.command match
                case e: Command.Explain => o.copy(command = e.copy(code = c))
                case _ => o
            )
        ),
      cmd("query")
        .text("ask the compiler about a file: hover, definition, references, completions (at <line>:<col>), symbols, diagnostics")
        .action((_, o) => o.copy(command = Command.Query("", "", None)))
        .children(
          arg[String]("<file.hgn>").action((f, o) =>
            o.command match
              case q: Command.Query => o.copy(command = q.copy(file = f))
              case _ => o
          ),
          arg[String]("<request>")
            .validate(r => if requests(r) then success else failure(s"unknown query `$r`; expected one of ${requests.mkString(", ")}"))
            .action((r, o) =>
              o.command match
                case q: Command.Query => o.copy(command = q.copy(request = r))
                case _ => o
            ),
          arg[String]("<line>:<col>")
            .optional()
            .validate(p => if position(p).isDefined then success else failure(s"expected a position `line:column`, got `$p`"))
            .action((p, o) =>
              o.command match
                case q: Command.Query => o.copy(command = q.copy(position = position(p)))
                case _ => o
            )
        ),
      cmd("repl")
        .text("an interactive session (reads the session from stdin when it is not a terminal)")
        .action((_, o) => o.copy(command = Command.Repl(Nil, batch = false)))
        .children(
          opt[Unit]("batch")
            .text("read the session from stdin without prompts or echo")
            .action((_, o) =>
              o.command match
                case r: Command.Repl => o.copy(command = r.copy(batch = true))
                case _ => o
            ),
          opt[Unit]("echo")
            .text("with --batch: write each input after its prompt, as a transcript")
            .action((_, o) =>
              o.command match
                case r: Command.Repl => o.copy(command = r.copy(echo = true))
                case _ => o
            ),
          arg[String]("<file.hgn>...")
            .optional()
            .unbounded()
            .action((f, o) =>
              o.command match
                case r: Command.Repl => o.copy(command = r.copy(files = r.files :+ f))
                case _ => o
            )
        ),
      cmd("lsp")
        .text("run the language server (LSP over stdin/stdout) for editors")
        .action((_, o) => o.copy(command = Command.Lsp)),
      note(""),
      opt[String]("facts")
        .valueName("<file>")
        .unbounded()
        .text("load ground facts for input relations (repeatable)")
        .action((f, o) => o.copy(run = o.run.copy(facts = o.run.facts :+ f))),
      opt[Seq[String]]("print-after")
        .valueName("<phase>,...")
        .unbounded()
        .text("print the program after these phases (`all` for every phase)")
        .validate(phases)
        .action((ps, o) => o.copy(settings = o.settings.copy(printAfter = o.settings.printAfter ++ ps))),
      opt[String]("stop-after")
        .valueName("<phase>")
        .text("stop compilation after this phase")
        .validate(p => phases(Seq(p)))
        .action((p, o) => o.copy(settings = o.settings.copy(stopAfter = Some(p)))),
      opt[Unit]("stats")
        .text("print compiler phase timings and evaluation statistics")
        .action((_, o) => o.copy(run = o.run.copy(stats = true))),
      opt[Unit]("all-relations")
        .text("print the facts of every relation (including fact constructors and demand relations)")
        .action((_, o) => o.copy(run = o.run.copy(allRelations = true))),
      opt[Unit]("color")
        .text("colour diagnostics")
        .action((_, o) => o.copy(display = o.display.copy(color = true))),
      opt[Unit]("no-color")
        .text("do not colour diagnostics")
        .action((_, o) => o.copy(display = o.display.copy(color = false))),
      opt[String]("error-format")
        .valueName("human|json")
        .text("how to print diagnostics: rendered for people (default) or as JSON lines")
        .validate(f => if f == "human" || f == "json" then success else failure(s"unknown error format `$f`; expected human or json"))
        .action((f, o) => o.copy(display = o.display.copy(json = f == "json"))),
      opt[Unit]("no-warnings")
        .text("suppress warnings")
        .action((_, o) => o.copy(display = o.display.copy(warnings = false))),
      opt[Unit]("no-prelude")
        .text("do not include the standard prelude (base types must then be declared with %builtin)")
        .action((_, o) => o.copy(settings = o.settings.copy(prelude = false))),
      opt[Unit]("new-meta")
        .hidden()
        .text("elaborate with the new meta level (redesign Phase B, in development)")
        .action((_, o) => o.copy(newMeta = true)),
      opt[Unit]("explain-termination")
        .text("print the termination argument of every recursive component (Section 10)")
        .action((_, o) => o.copy(settings = o.settings.copy(explainTermination = true))),
      checkConfig(o =>
        o.command match
          case Command.Help => failure("no command given")
          case Command.Explain("", false) => failure("`explain` needs a code, or --list")
          case Command.Query(_, r, None) if positional(r) => failure(s"`$r` needs a position `line:column`")
          case _ => success
      )
    )

  val usage: String = OParser.usage(parser)

  private def positional = Set("hover", "definition", "references", "completions")
  private def requests = positional ++ Set("symbols", "diagnostics")

  private def position(s: String): Option[(Int, Int)] = s.split(":") match
    case Array(l, c) => for line <- l.toIntOption if line >= 1; col <- c.toIntOption if col >= 1 yield (line, col)
    case _ => None

  /** Parses `args`; `Left` carries an error message. `--help` yields [[Command.Help]]. */
  def parse(args: List[String], defaultColor: Boolean = false): Either[String, Options] =
    val init = Options(Command.Help, Settings(), RunOptions(), Display(color = defaultColor))
    if args.contains("--help") || args.contains("-h") then return Right(init)
    val (result, effects) = OParser.runParser(parser, args, init)
    val errors = effects.collect { case OEffect.ReportError(msg) => msg }
    result match
      case Some(opts) if errors.isEmpty => Right(opts)
      case _ => Left(errors.headOption.getOrElse("invalid command line"))
