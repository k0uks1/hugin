package hugin.fuzz

import hugin.cli.Main
import hugin.compiler.{Compiler, Context, ImportsPhase, Parsed, Settings, SourceLoader}
import hugin.util.*
import org.scalacheck.{Prop, Test}
import org.scalacheck.rng.Seed

import java.nio.file.{Files, Path}
import java.util.concurrent.{ExecutionException, FutureTask, TimeUnit, TimeoutException}
import scala.concurrent.duration.*
import scala.jdk.CollectionConverters.*

/** Settings of the fuzz suites. `sbt test` runs every property a few times from a fixed seed (the short
 *  run); `sbt fuzz` sets the system property `hugin.fuzz.long` and runs 2000 tests per property from a
 *  random seed. The environment variables `HUGIN_FUZZ_COUNT` (tests per property) and `HUGIN_FUZZ_SEED`
 *  (`random`, a number, or the base64 ScalaCheck seed printed by a failing run) override both. */
object Fuzz:
  private def setting(prop: String, env: String): Option[String] =
    sys.props.get(prop).orElse(sys.env.get(env)).map(_.trim).filter(_.nonEmpty)

  val long: Boolean = sys.props.get("hugin.fuzz.long").contains("true")

  val count: Option[Int] = setting("hugin.fuzz.count", "HUGIN_FUZZ_COUNT").map(_.toInt).orElse(Option.when(long)(2000))

  val seed: String = setting("hugin.fuzz.seed", "HUGIN_FUZZ_SEED").orElse(Option.when(long)("random")) match
    case None => Seed(20261006L).toBase64
    case Some("random") => Seed.random().toBase64
    case Some(n) if n.forall(_.isDigit) => Seed(n.toLong).toBase64
    case Some(s) => s

  /** Time limit for one compilation or run; generous, since CI machines are slow and shared. */
  val limit: FiniteDuration = 20.seconds

  /** Failing programs (after shrinking) are written here; the nightly workflow uploads the directory. */
  val failures: Path = Path.of("target", "fuzz-failures")

  /** A scratch copy of the corpus. Programs are compiled as if they were in the directory of the corpus
   *  file they come from, so that their relative `%import`s find the same libraries; imports that resolve
   *  outside the sandbox are never read. */
  lazy val sandbox: Path =
    val dir = Files.createTempDirectory("hugin-fuzz").toRealPath()
    for root <- List("examples", "tests"); p <- Files.walk(Path.of(root)).iterator().asScala.toList if Files.isRegularFile(p) do
      val target = dir.resolve(p.toString)
      Files.createDirectories(target.getParent)
      Files.copy(p, target)
    dir

  /** Paths a program may read: the bundled standard library and files inside the sandbox. */
  def readable(path: String): Boolean =
    path.startsWith(SourceLoader.StdlibPrefix) ||
      scala.util.Try(Path.of(path).toAbsolutePath.normalize.startsWith(sandbox)).getOrElse(false)

  /** Loads imports from the sandbox only. */
  val loader: SourceLoader = path => if readable(path) then SourceLoader.files.load(path) else None

  enum Failure:
    case Crashed(e: Throwable)
    case TimedOut

    def describe: String = this match
      case Crashed(e) =>
        val sw = java.io.StringWriter()
        e.printStackTrace(java.io.PrintWriter(sw))
        s"uncaught exception: ${sw.toString.linesIterator.take(16).mkString("\n")}"
      case TimedOut => s"no result within $limit"

  /** Runs `body` on a fresh thread with the launcher's stack size (`-Xss64m`). After the time limit the
   *  thread is interrupted (the engine stops at its next round) and abandoned. */
  def guarded[A](body: => A): Either[Failure, A] =
    val task = FutureTask[A](() => body)
    val thread = Thread(null, task, "hugin-fuzz", 64L << 20)
    thread.setDaemon(true)
    thread.start()
    try Right(task.get(limit.toMillis, TimeUnit.MILLISECONDS))
    catch
      case e: ExecutionException => Left(Failure.Crashed(e.getCause))
      case _: TimeoutException =>
        thread.interrupt()
        Left(Failure.TimedOut)

  /** Where a program is written: `fuzz.hgn` in its directory inside the sandbox. */
  def file(program: Program): Path =
    val dir = sandbox.resolve(program.dir)
    Files.createDirectories(dir)
    dir.resolve("fuzz.hgn")

  /** Compiles a program in-process with the sandbox loader. */
  def compile(program: Program, settings: Settings = Settings()): Context =
    val source = SourceFile.virtual(file(program).toString, program.code)
    Compiler.compileParsed(Parsed(source), settings, loader, _ => ())

  /** True if one of the program's `%import`s resolves outside the sandbox; the CLI (which reads imports
   *  from disk) is then not run on it. */
  def escapes(program: Program): Boolean =
    val parsed = Parsed(SourceFile.virtual(file(program).toString, program.code))
    ImportsPhase.importsIn(parsed.program).exists(i => !readable(SourceLoader.resolve(parsed.source.path, i.path)))

  /** Exit code, stdout and stderr of one CLI invocation. */
  final case class Invocation(exit: Int, out: String, err: String)

  /** Runs `hugin <command> <file> <args>` on the program, written to its sandbox file (always the same
   *  path, so that the output of two invocations can be compared). */
  def cli(command: String, program: Program, args: List[String] = Nil): Either[Failure, Invocation] =
    val path = file(program)
    Files.writeString(path, program.code)
    val facts = program.facts.toList.flatMap { f =>
      val p = path.resolveSibling("fuzz.facts")
      Files.writeString(p, f)
      List("--facts", p.toString)
    }
    guarded {
      val out = StringBuilder()
      val err = StringBuilder()
      val code = Main.run(List(command, path.toString, "--no-color") ++ facts ++ args, s => out ++= s += '\n', s => err ++= s += '\n')
      Invocation(code, out.toString, err.toString)
    }

  /** Problems with the diagnostics of an in-process compilation: spans outside their file, rendering
   *  that throws (with and without colours), errors without a diagnostic. */
  def diagnosticProblems(program: Program): List[String] =
    guarded {
      val c = compile(program)
      val ds = c.reporter.diagnostics
      val spans =
        for
          d <- ds
          s <- d.labels.map(_.span) ++ d.origin.frames.map(_.span)
          if s.exists && (s.start < 0 || s.end < s.start || s.end > s.source.content.length)
        yield s"diagnostic `${d.message}` has span ${s.start}..${s.end} outside `${s.source.path}` (length ${s.source.content.length})"
      for color <- List(false, true) do
        val r = DiagnosticRenderer(color)
        ds.foreach(r.render)
        r.summary(c.reporter)
      val silent =
        Option.when(c.reporter.hasErrors && !ds.exists(_.severity == Severity.Error))("errors were reported without a diagnostic")
      spans ++ silent
    } match
      case Left(f) => List(s"compile: ${f.describe}")
      case Right(ps) => ps

  /** Robustness properties of `check` and `run` (issue #7); the returned list of problems is empty if
   *  they hold. `check` must finish in time with exit code 0 or 1, deterministically, and say why it
   *  failed; diagnostics must have spans inside their file and render. `run` must not crash
   *  or exit with another code; with `mustRun`, a program accepted by `check` must also run to completion
   *  (a timeout is a problem), otherwise a run that exceeds the time limit is tolerated (a mutation may
   *  legitimately raise a bound to 2^63). */
  def robustness(program: Program, mustRun: Boolean): List[String] =
    def exitCode(what: String, i: Invocation) =
      Option.when(i.exit != 0 && i.exit != 1)(s"$what: exit code ${i.exit}\n${i.err}")
    val inProcess = diagnosticProblems(program)
    val viaCli =
      if guarded(escapes(program)).getOrElse(false) then Nil
      else
        cli("check", program) match
          case Left(f) => List(s"check: ${f.describe}")
          case Right(first) =>
            val again = cli("check", program) match
              case Left(f) => Some(s"second check: ${f.describe}")
              case Right(second) =>
                Option.when(second != first)(s"check is not deterministic:\n--- first\n${first.err}\n--- second\n${second.err}")
            val silent = Option.when(first.exit == 1 && first.err.isBlank)("check failed without a diagnostic")
            val run = cli("run", program) match
              case Left(Failure.TimedOut) if !mustRun || first.exit != 0 => None
              case Left(f) => Some(s"run: ${f.describe}")
              case Right(r) =>
                exitCode("run", r).orElse(
                  Option.when(mustRun && first.exit == 0 && r.exit != 0)(s"accepted by check, but run failed:\n${r.err}")
                )
            exitCode("check", first).toList ++ again ++ silent ++ run
    inProcess ++ viaCli

/** A program with optional input facts, printed in full when a property fails. `dir` is the directory
 *  (relative to the repository) whose libraries its imports refer to. */
final case class Program(code: String, facts: Option[String] = None, dir: String = "."):
  override def toString: String =
    s"\n----- program\n$code\n-----" + facts.map(f => s"\n----- facts\n$f\n-----").getOrElse("")

/** Base of the fuzz suites: test counts and seed from [[Fuzz]], failing programs saved for the CI artifact. */
trait FuzzSuite extends munit.ScalaCheckSuite:
  /** Tests per property in the short run that is part of `sbt test`. */
  def shortCount: Int = 10

  override def scalaCheckTestParameters: Test.Parameters =
    super.scalaCheckTestParameters.withMinSuccessfulTests(Fuzz.count.getOrElse(shortCount)).withWorkers(1)

  override def scalaCheckInitialSeed: String = Fuzz.seed

  override def beforeAll(): Unit =
    for n <- Fuzz.count do println(s"${getClass.getSimpleName}: $n tests per property, seed ${Fuzz.seed}")

  /** Passes if `problems` is empty; otherwise saves the program as `target/fuzz-failures/<suite>/<name>.hgn`
   *  (overwritten while shrinking, so the file ends up holding the minimised program). */
  def verdict(name: String, program: Program, problems: List[String]): Prop =
    if problems.isEmpty then Prop.passed
    else
      val dir = Fuzz.failures.resolve(getClass.getSimpleName)
      Files.createDirectories(dir)
      val base = name.replaceAll("[^A-Za-z0-9]+", "-")
      Files.writeString(dir.resolve(s"$base.hgn"), program.code)
      program.facts.foreach(f => Files.writeString(dir.resolve(s"$base.facts"), f))
      Files.writeString(dir.resolve(s"$base.txt"), s"seed: ${Fuzz.seed}\ndirectory: ${program.dir}\n\n${problems.mkString("\n\n")}\n")
      problems.foldLeft(Prop.falsified)(_ :| _)
