package hugin.cli

import hugin.util.*
import hugin.compiler.*
import hugin.query.*
import hugin.repl.{Repl, Session}
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
      ErrorCodes.lookup(code.toUpperCase) match
        case Some((c, title, text)) =>
          out(s"$c: $title\n\n$text")
          ExitCode.Ok
        case None =>
          err(s"error: unknown diagnostic code `$code`")
          ExitCode.Usage
    case Command.Check(file) => compileAndRun(file, opts, out, err, evaluate = false)
    case Command.Run(file) => compileAndRun(file, opts, out, err, evaluate = true)
    case Command.Query(file, request, position) => query(file, request, position, opts, out, err)
    case Command.Repl(files, batch) =>
      val session = Session(opts.settings, opts.run.budget, opts.run.stats)
      val ok = Repl.run(session, files, opts.run.facts, batch, opts.settings.color, in, out, err)
      if ok then ExitCode.Ok else ExitCode.Errors

  /** Loads a file into the database; false if it does not exist. */
  private def load(db: Database, file: String): Boolean =
    val path = Path.of(file)
    if Files.isRegularFile(path) then
      db.set(SourceText, file, Files.readString(path))
      true
    else false

  private def render(diags: List[Diagnostic], settings: Settings, err: String => Unit): Unit =
    val renderer = DiagnosticRenderer(settings.color)
    diags.foreach(d => err(renderer.render(d)))
    val r = Reporter()
    diags.foreach(r.report)
    val summary = renderer.summary(r)
    if summary.nonEmpty then err(summary)

  private def compileAndRun(file: String, opts: Options, out: String => Unit, err: String => Unit, evaluate: Boolean): Int =
    given db: Database = Database()
    if !load(db, file) then
      err(s"error: no such file `$file`")
      return ExitCode.Usage
    val key = CompileKey(file, opts.settings)
    val compiled = db(Compile, key)
    compiled.printed.foreach(out)
    if compiled.hasErrors || !evaluate || opts.settings.stopAfter.isDefined then
      render(compiled.diagnostics, opts.settings, err)
      return if compiled.hasErrors then ExitCode.Errors else ExitCode.Ok
    val facts = opts.run.facts.filter { f =>
      val ok = load(db, f)
      if !ok then err(s"error: no such facts file `$f`")
      ok
    }
    val outcome = db(Evaluate, EvaluateKey(key, facts, opts.run.budget, opts.run.allRelations))
    render(compiled.diagnostics ++ outcome.diagnostics, opts.settings, err)
    outcome.result match
      case None => ExitCode.Errors
      case Some(res) =>
        res.output.foreach(out)
        if opts.run.stats then res.statistics.foreach(err)
        ExitCode.Ok

  private def query(
      file: String,
      request: String,
      position: Option[(Int, Int)],
      opts: Options,
      out: String => Unit,
      err: String => Unit
  ): Int =
    given db: Database = Database()
    if !load(db, file) then
      err(s"error: no such file `$file`")
      return ExitCode.Usage
    val key = CompileKey(file, opts.settings)
    def loc(s: Span) = s"${s.source.path}:${s.startLine + 1}:${s.startCol + 1}"
    val offset = position.flatMap((l, c) => db(Parse, file).source.offset(l - 1, c - 1))
    if position.isDefined && offset.isEmpty then
      err(s"error: position ${position.get._1}:${position.get._2} is outside `$file`")
      return ExitCode.Usage
    request match
      case "hover" => out(Ide.hover(key, offset.get).getOrElse("(no information)"))
      case "definition" => out(Ide.definition(key, offset.get).map(loc).getOrElse("(no definition)"))
      case "references" => Ide.references(key, offset.get).foreach(s => out(loc(s)))
      case "symbols" =>
        for s <- Ide.symbols(key) do out(s"${loc(s.span)}  ${s.kind} ${s.name}${s.container.map(c => s"  (in $c)").getOrElse("")}")
      case "diagnostics" => render(Ide.diagnostics(key), opts.settings, out)
    ExitCode.Ok
