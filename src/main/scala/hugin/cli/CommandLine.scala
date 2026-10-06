package hugin.cli

import hugin.compiler.{Compiler, Settings}
import scopt.{OEffect, OParser}

/** What the user asked for. */
enum Command:
  case Run(file: String)
  case Check(file: String)
  case Phases
  case Explain(code: String)
  case Help

/** Options of `hugin run` that do not influence compilation. */
final case class RunOptions(
    /** Files of ground facts for input relations. */
    facts: List[String] = Nil,
    /** Round budget for components with `%partial` relations (Section 9.7); `None` is unbounded. */
    budget: Option[Int] = None,
    /** Print evaluation statistics to stderr. */
    stats: Boolean = false,
    /** Print every relation, including constructors and demand relations. */
    allRelations: Boolean = false
)

final case class Options(command: Command, settings: Settings, run: RunOptions)

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
        .text("explain a diagnostic code (e.g. E0401)")
        .action((_, o) => o.copy(command = Command.Explain("")))
        .children(arg[String]("<code>").action((c, o) => o.copy(command = Command.Explain(c)))),
      note(""),
      opt[String]("facts")
        .valueName("<file>")
        .unbounded()
        .text("load ground facts for input relations (repeatable)")
        .action((f, o) => o.copy(run = o.run.copy(facts = o.run.facts :+ f))),
      opt[Int]("budget")
        .valueName("<n>")
        .text("round budget for components with %partial relations (default: unbounded)")
        .validate(b => if b >= 0 then success else failure(s"--budget expects a natural number, got `$b`"))
        .action((b, o) => o.copy(run = o.run.copy(budget = Some(b)))),
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
        .text("print evaluation statistics")
        .action((_, o) => o.copy(run = o.run.copy(stats = true))),
      opt[Unit]("all-relations")
        .text("print the facts of every relation (including constructors and demand relations)")
        .action((_, o) => o.copy(run = o.run.copy(allRelations = true))),
      opt[Unit]("color")
        .text("colour diagnostics")
        .action((_, o) => o.copy(settings = o.settings.copy(color = true))),
      opt[Unit]("no-color")
        .text("do not colour diagnostics")
        .action((_, o) => o.copy(settings = o.settings.copy(color = false))),
      opt[Unit]("no-warnings")
        .text("suppress warnings")
        .action((_, o) => o.copy(settings = o.settings.copy(warnings = false))),
      opt[Unit]("lint")
        .text("enable advisory checks (W0004)")
        .action((_, o) => o.copy(settings = o.settings.copy(lint = true))),
      checkConfig(o =>
        o.command match
          case Command.Help => failure("no command given")
          case _ => success
      )
    )

  val usage: String = OParser.usage(parser)

  /** Parses `args`; `Left` carries an error message. `--help` yields [[Command.Help]]. */
  def parse(args: List[String], defaultColor: Boolean = false): Either[String, Options] =
    val init = Options(Command.Help, Settings(color = defaultColor), RunOptions())
    if args.contains("--help") || args.contains("-h") then return Right(init)
    val (result, effects) = OParser.runParser(parser, args, init)
    val errors = effects.collect { case OEffect.ReportError(msg) => msg }
    result match
      case Some(opts) if errors.isEmpty => Right(opts)
      case _ => Left(errors.headOption.getOrElse("invalid command line"))
