package hugin.cli

import hugin.util.*
import hugin.compiler.*
import java.nio.file.{Files, Path}

/** Command-line interface. */
object Main:
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

  def main(args: Array[String]): Unit =
    val out = java.io.PrintStream(java.io.FileOutputStream(java.io.FileDescriptor.out), true, "UTF-8")
    val err = java.io.PrintStream(java.io.FileOutputStream(java.io.FileDescriptor.err), true, "UTF-8")
    sys.exit(run(args.toList, s => out.println(s), s => err.println(s)))

  /** Entry point usable from tests; returns the exit code. */
  def run(args: List[String], out: String => Unit, err: String => Unit): Int =
    var settings = Settings(color = System.console() != null && System.getenv("NO_COLOR") == null)
    var stats = false
    var allRelations = false
    var positional = List.empty[String]
    var rest = args
    var bad = false
    while rest.nonEmpty do
      rest match
        case "--facts" :: f :: tl => settings = settings.copy(facts = settings.facts :+ f); rest = tl
        case "--budget" :: n :: tl =>
          n.toIntOption match
            case Some(b) if b >= 0 => settings = settings.copy(budget = Some(b))
            case _ => err(s"error: --budget expects a natural number, got `$n`"); bad = true
          rest = tl
        case "--print-after" :: p :: tl => settings = settings.copy(printAfter = settings.printAfter ++ p.split(",").map(_.trim)); rest = tl
        case "--stop-after" :: p :: tl => settings = settings.copy(stopAfter = Some(p)); rest = tl
        case "--stats" :: tl => stats = true; rest = tl
        case "--all-relations" :: tl => allRelations = true; rest = tl
        case "--color" :: tl => settings = settings.copy(color = true); rest = tl
        case "--no-color" :: tl => settings = settings.copy(color = false); rest = tl
        case "--lint" :: tl => settings = settings.copy(lint = true); rest = tl
        case "--no-warnings" :: tl => settings = settings.copy(warnings = false); rest = tl
        case ("-h" | "--help") :: tl => out(usage); return 0
        case opt :: tl if opt.startsWith("--") => err(s"error: unknown option `$opt`"); bad = true; rest = tl
        case x :: tl => positional = positional :+ x; rest = tl
        case Nil =>
    if bad then { err(usage); return 2 }
    val known = Compiler.allPhaseNames.toSet + "all"
    (settings.printAfter ++ settings.stopAfter).find(p => !known(p)) match
      case Some(p) =>
        err(s"error: unknown phase `$p`; see `hugin phases`")
        return 2
      case None =>
    positional match
      case List("phases") =>
        for p <- Compiler.phasePlan do
          p match
            case List(single) => out(f"  ${single.phaseName}%-14s ${single.description}")
            case group =>
              out(s"  (fused: ${group.map(_.phaseName).mkString(" + ")})")
              group.foreach(m => out(f"    ${m.phaseName}%-12s ${m.description}"))
        0
      case List("explain", code) =>
        ErrorCodes.lookup(code.toUpperCase) match
          case Some((c, title, text)) => out(s"$c: $title\n\n$text"); 0
          case None => err(s"error: unknown diagnostic code `$code`"); 2
      case List(cmd @ ("run" | "check"), file) =>
        val path = Path.of(file)
        if !Files.exists(path) then { err(s"error: no such file `$file`"); return 2 }
        val src = SourceFile.fromPath(path)
        val renderer = DiagnosticRenderer(settings.color)
        val c = Compiler.compile(src, settings, out)
        def flush(): Unit =
          c.reporter.sorted.foreach(d => err(renderer.render(d)))
          val s = renderer.summary(c.reporter)
          if s.nonEmpty then err(s)
        if c.reporter.hasErrors then { flush(); return 1 }
        if cmd == "check" || settings.stopAfter.isDefined then { flush(); return 0 }
        val facts = settings.facts.flatMap { f =>
          val p = Path.of(f)
          if Files.exists(p) then Some(SourceFile.fromPath(p))
          else { err(s"error: no such facts file `$f`"); None }
        }
        Runner.run(c, facts, settings.budget, allRelations) match
          case None => flush(); 1
          case Some(res) =>
            flush()
            res.output.foreach(out)
            if stats then
              for s <- res.stats if s.rounds > 0 || s.truncated do
                err(s"(* {${s.rels.mkString(", ")}}: ${s.rounds} round(s)${if s.truncated then ", truncated" else ""} *)")
            0
      case _ => err(usage); 2
