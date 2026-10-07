package hugin.cli

import hugin.util.*
import hugin.compiler.*
import hugin.query.*
import hugin.repl.{Repl, Session}
import hugin.lsp.HuginLanguageServer
import hugin.runtime.Evaluation
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

  /** Runs one command; returns the exit code. `out` receives results, `err` diagnostics; `in` is read by
   *  `hugin repl` when it is not interactive. */
  def run(args: List[String], out: String => Unit, err: String => Unit, in: java.io.InputStream = System.in): Int =
    val defaultColor = System.console() != null && System.getenv("NO_COLOR") == null
    CommandLine.parse(args, defaultColor) match
      case Left(msg) =>
        err(s"error: $msg")
        err(CommandLine.usage)
        ExitCode.Usage
      case Right(opts) => dispatch(opts, out, err, in)

  private def dispatch(opts: Options, out: String => Unit, err: String => Unit, in: java.io.InputStream): Int = opts.command match
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
      ErrorCodes.explain(code) match
        case Some(text) =>
          out(text)
          ExitCode.Ok
        case None =>
          err(s"error: unknown diagnostic code `$code`")
          ExitCode.Usage
    case Command.Check(file) if opts.newMeta => newMeta(file, opts, out, err, print = false)
    case Command.Run(file) if opts.newMeta => newMeta(file, opts, out, err, print = true)
    case Command.Check(file) => compileAndRun(file, opts, out, err, evaluate = false)
    case Command.Run(file) => compileAndRun(file, opts, out, err, evaluate = true)
    case Command.Query(file, request, position) => query(file, request, position, opts, out, err)
    case Command.Repl(files, batch, echo) =>
      val session = Session(opts.settings, opts.run.stats)
      val ok = Repl.run(session, files, opts.run.facts, batch, echo, opts.display, in, out, err)
      if ok then ExitCode.Ok else ExitCode.Errors
    case Command.Lsp =>
      // the protocol owns stdout; anything else printed there would corrupt it
      val protocol = java.io.FileOutputStream(java.io.FileDescriptor.out)
      System.setOut(System.err)
      HuginLanguageServer.serve(System.in, protocol)

  /** Loads a file into the database; false if it does not exist. */
  private def load(db: Database, file: String): Boolean =
    val path = Path.of(file)
    if Files.isRegularFile(path) then
      db.set(SourceText, file, Files.readString(path))
      true
    else false

  /** Runs `body` on a new database holding the program `file`; a usage error if it does not exist. */
  private def withProgram(file: String, err: String => Unit)(body: Database ?=> Int): Int =
    given db: Database = Database()
    if load(db, file) then body
    else
      err(s"error: no such file `$file`")
      ExitCode.Usage

  private def render(all: List[Diagnostic], display: Display, err: String => Unit): Unit =
    val diags = display.shown(all)
    val renderer = DiagnosticRenderer(display.color)
    diags.foreach(d => err(renderer.render(d)))
    val r = Reporter()
    diags.foreach(r.report)
    val summary = renderer.summary(r)
    if summary.nonEmpty then err(summary)

  /** The new meta level (redesign Phase B): elaborates the file; `print` writes the elaborated program
   *  with its object items staged. */
  private def newMeta(file: String, opts: Options, out: String => Unit, err: String => Unit, print: Boolean): Int =
    val path = Path.of(file)
    if !Files.isRegularFile(path) then
      err(s"error: no such file `$file`")
      ExitCode.Usage
    else
      val result = hugin.core.NewMeta.elaborate(SourceFile(file, Files.readString(path)))
      if print then result.output.foreach(out)
      render(result.diagnostics, opts.display, err)
      if result.hasErrors then ExitCode.Errors else ExitCode.Ok

  private def compileAndRun(file: String, opts: Options, out: String => Unit, err: String => Unit, evaluate: Boolean): Int =
    withProgram(file, err) {
      val key = CompileKey(file, opts.settings)
      val compiled = summon[Database](Compile, key)
      compiled.printed.foreach(out)
      if opts.run.stats then err(phaseTimings(compiled))
      if compiled.hasErrors || !evaluate || opts.settings.stopAfter.isDefined then
        render(compiled.diagnostics, opts.display, err)
        if compiled.hasErrors then ExitCode.Errors else ExitCode.Ok
      else evaluateProgram(key, compiled, opts, out, err)
    }

  private def evaluateProgram(key: CompileKey, compiled: Compiled, opts: Options, out: String => Unit, err: String => Unit)(using
      db: Database
  ): Int =
    val facts = opts.run.facts.filter { f =>
      val ok = load(db, f)
      if !ok then err(s"error: no such facts file `$f`")
      ok
    }
    val outcome = db(Evaluate, EvaluateKey(key, facts, opts.run.allRelations))
    render(compiled.diagnostics ++ outcome.diagnostics, opts.display, err)
    outcome.result match
      case None => ExitCode.Errors
      case Some(res) =>
        res.output.foreach(out)
        if opts.run.stats then res.statistics.foreach(err)
        ExitCode.Ok

  /** One line with the time each compiler phase took. */
  private def phaseTimings(c: Compiled): String =
    val ts = c.context.timings.toList
    val total = ts.map(_._2).sum
    def ms(ns: Long) = f"${ns / 1e6}%.1f"
    s"(* compile ${ms(total)} ms: ${ts.map((p, ns) => s"$p ${ms(ns)}").mkString(", ")} *)"

  private def query(
      file: String,
      request: String,
      position: Option[(Int, Int)],
      opts: Options,
      out: String => Unit,
      err: String => Unit
  ): Int = withProgram(file, err) {
    val key = CompileKey(file, opts.settings)
    val offset = position.flatMap((l, c) => summon[Database](Parse, file).source.offset(l - 1, c - 1))
    if position.isDefined && offset.isEmpty then
      err(s"error: position ${position.get._1}:${position.get._2} is outside `$file`")
      ExitCode.Usage
    else answer(key, request, offset, opts, out)
  }

  private def answer(key: CompileKey, request: String, offset: Option[Int], opts: Options, out: String => Unit)(using Database): Int =
    request match
      case "hover" => out(Ide.hover(key, offset.get).getOrElse("(no information)"))
      case "definition" => out(Ide.definition(key, offset.get).map(_.show).getOrElse("(no definition)"))
      case "references" => Ide.references(key, offset.get).foreach(s => out(s.show))
      case "completions" => Ide.completions(key, offset.get).foreach(c => out(s"${c.label}  (${c.kind})  ${c.detail}"))
      case "symbols" =>
        for s <- Ide.symbols(key) do out(s"${s.span.show}  ${s.kind.describe} ${s.name}${s.container.map(c => s"  (in $c)").getOrElse("")}")
      case "diagnostics" => render(Ide.diagnostics(key), opts.display, out)
    ExitCode.Ok
