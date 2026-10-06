package hugin.cli

import hugin.util.*
import hugin.compiler.*
import java.nio.file.{Files, Path}

/** Process exit codes. */
object ExitCode:
  val Ok = 0

  /** Compilation, input or evaluation errors were reported. */
  val Errors = 1

  /** The command line was malformed. */
  val Usage = 2

/** Command-line entry point. */
object Main:
  def main(args: Array[String]): Unit =
    val out = java.io.PrintStream(java.io.FileOutputStream(java.io.FileDescriptor.out), true, "UTF-8")
    val err = java.io.PrintStream(java.io.FileOutputStream(java.io.FileDescriptor.err), true, "UTF-8")
    sys.exit(run(args.toList, s => out.println(s), s => err.println(s)))

  /** Runs one command; returns the exit code. `out` receives results, `err` diagnostics. */
  def run(args: List[String], out: String => Unit, err: String => Unit): Int =
    val defaultColor = System.console() != null && System.getenv("NO_COLOR") == null
    CommandLine.parse(args, defaultColor) match
      case Left(msg) =>
        err(s"error: $msg")
        err(CommandLine.usage)
        ExitCode.Usage
      case Right(opts) => dispatch(opts, out, err)

  private def dispatch(opts: Options, out: String => Unit, err: String => Unit): Int = opts.command match
    case Command.Help =>
      out(CommandLine.usage)
      ExitCode.Ok
    case Command.Phases =>
      for p <- Compiler.phasePlan do
        p match
          case List(single) => out(f"  ${single.phaseName}%-14s ${single.description}")
          case group =>
            out(s"  (fused: ${group.map(_.phaseName).mkString(" + ")})")
            group.foreach(m => out(f"    ${m.phaseName}%-12s ${m.description}"))
      ExitCode.Ok
    case Command.Explain(code) =>
      ErrorCodes.lookup(code.toUpperCase) match
        case Some((c, title, text)) =>
          out(s"$c: $title\n\n$text")
          ExitCode.Ok
        case None =>
          err(s"error: unknown diagnostic code `$code`")
          ExitCode.Usage
    case Command.Check(file) => compileAndRun(file, opts, out, err, evaluate = false)
    case Command.Run(file) => compileAndRun(file, opts, out, err, evaluate = true)

  private def compileAndRun(file: String, opts: Options, out: String => Unit, err: String => Unit, evaluate: Boolean): Int =
    readSource(file) match
      case None =>
        err(s"error: no such file `$file`")
        ExitCode.Usage
      case Some(src) =>
        val settings = opts.settings
        val renderer = DiagnosticRenderer(settings.color)
        val c = Compiler.compile(src, settings, out)
        def flushDiagnostics(): Unit =
          c.reporter.sorted.foreach(d => err(renderer.render(d)))
          val summary = renderer.summary(c.reporter)
          if summary.nonEmpty then err(summary)
        if c.reporter.hasErrors then
          flushDiagnostics()
          ExitCode.Errors
        else if !evaluate || settings.stopAfter.isDefined then
          flushDiagnostics()
          ExitCode.Ok
        else
          val factFiles = opts.run.facts.flatMap { f =>
            val s = readSource(f)
            if s.isEmpty then err(s"error: no such facts file `$f`")
            s
          }
          Runner.run(c, factFiles, opts.run.budget, opts.run.allRelations) match
            case None =>
              flushDiagnostics()
              ExitCode.Errors
            case Some(res) =>
              flushDiagnostics()
              res.output.foreach(out)
              if opts.run.stats then
                for s <- res.stats if s.rounds > 0 || s.truncated do
                  err(s"(* {${s.rels.mkString(", ")}}: ${s.rounds} round(s)${if s.truncated then ", truncated" else ""} *)")
              ExitCode.Ok

  private def readSource(file: String): Option[SourceFile] =
    val path = Path.of(file)
    if Files.isRegularFile(path) then Some(SourceFile.fromPath(path)) else None
