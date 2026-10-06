package hugin.cli

import hugin.compiler.{Compiler, Settings}

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

/** Parses command-line arguments. Pure, so that it can be tested in isolation. */
object CommandLine:
  val usage: String =
    """usage: hugin <command> [options] <file.hgn>
      |
      |commands:
      |  run <file>          compile and evaluate; print output relations and query answers
      |  check <file>        compile only and report diagnostics
      |  phases              list the compiler phases
      |  explain <code>      explain a diagnostic code (e.g. E0401)
      |
      |options:
      |  --facts <file>      load ground facts for input relations (repeatable)
      |  --budget <n>        round budget for components with %partial relations (default: unbounded)
      |  --print-after <p>   print the program after phase p (comma-separated, repeatable; `all`)
      |  --stop-after <p>    stop compilation after phase p
      |  --stats             print evaluation statistics
      |  --all-relations     print the facts of every relation (including constructors and demand relations)
      |  --color / --no-color
      |  --no-warnings       suppress warnings
      |  --lint              enable advisory checks (W0004)
      |""".stripMargin

  /** Parses `args`; `Left` carries an error message. */
  def parse(args: List[String], defaultColor: Boolean = false): Either[String, Options] =
    var settings = Settings(color = defaultColor)
    var run = RunOptions()
    val positional = List.newBuilder[String]

    def loop(rest: List[String]): Either[String, Unit] = rest match
      case Nil => Right(())
      case ("-h" | "--help") :: _ => Left("help")
      case "--facts" :: f :: tl => run = run.copy(facts = run.facts :+ f); loop(tl)
      case "--budget" :: n :: tl =>
        n.toIntOption.filter(_ >= 0) match
          case Some(b) => run = run.copy(budget = Some(b)); loop(tl)
          case None => Left(s"--budget expects a natural number, got `$n`")
      case "--print-after" :: p :: tl =>
        settings = settings.copy(printAfter = settings.printAfter ++ p.split(",").map(_.trim).filter(_.nonEmpty))
        loop(tl)
      case "--stop-after" :: p :: tl => settings = settings.copy(stopAfter = Some(p)); loop(tl)
      case "--stats" :: tl => run = run.copy(stats = true); loop(tl)
      case "--all-relations" :: tl => run = run.copy(allRelations = true); loop(tl)
      case "--color" :: tl => settings = settings.copy(color = true); loop(tl)
      case "--no-color" :: tl => settings = settings.copy(color = false); loop(tl)
      case "--lint" :: tl => settings = settings.copy(lint = true); loop(tl)
      case "--no-warnings" :: tl => settings = settings.copy(warnings = false); loop(tl)
      case List(opt @ ("--facts" | "--budget" | "--print-after" | "--stop-after")) => Left(s"option `$opt` expects an argument")
      case opt :: _ if opt.startsWith("--") => Left(s"unknown option `$opt`")
      case x :: tl => positional += x; loop(tl)

    loop(args) match
      case Left("help") => Right(Options(Command.Help, settings, run))
      case Left(msg) => Left(msg)
      case Right(()) =>
        val known = Compiler.allPhaseNames.toSet + "all"
        (settings.printAfter ++ settings.stopAfter).find(p => !known(p)) match
          case Some(p) => Left(s"unknown phase `$p`; see `hugin phases`")
          case None =>
            positional.result() match
              case List("run", file) => Right(Options(Command.Run(file), settings, run))
              case List("check", file) => Right(Options(Command.Check(file), settings, run))
              case List("phases") => Right(Options(Command.Phases, settings, run))
              case List("explain", code) => Right(Options(Command.Explain(code), settings, run))
              case Nil => Left("no command given")
              case other => Left(s"cannot understand `${other.mkString(" ")}`")
