package hugin.fuzz

import hugin.cli.Main
import hugin.compiler.{Compiler, Settings}
import hugin.util.*
import org.scalacheck.{Prop, Test}
import org.scalacheck.rng.Seed

import java.nio.file.{Files, Path}
import java.util.concurrent.{ExecutionException, FutureTask, TimeUnit, TimeoutException}
import scala.concurrent.duration.*

/** Settings of the fuzz suites. `sbt test` runs every property a few times from a fixed seed; `sbt fuzz`
 *  sets the system properties `hugin.fuzz.count` (tests per property) and `hugin.fuzz.seed` (`random`, a
 *  number, or a base64 ScalaCheck seed as printed by a failing run). */
object Fuzz:
  val count: Option[Int] = sys.props.get("hugin.fuzz.count").map(_.toInt)

  val seed: String = sys.props.get("hugin.fuzz.seed") match
    case None => Seed(20261006L).toBase64
    case Some("random") => Seed.random().toBase64
    case Some(n) if n.forall(_.isDigit) => Seed(n.toLong).toBase64
    case Some(s) => s

  /** Time limit for one compilation or run; generous, since CI machines are slow and shared. */
  val limit: FiniteDuration = 20.seconds

  /** Failing programs (after shrinking) are written here; the nightly workflow uploads the directory. */
  val failures: Path = Path.of("target", "fuzz-failures")

  private lazy val scratch: Path = Files.createTempDirectory("hugin-fuzz")

  enum Failure:
    case Crashed(e: Throwable)
    case TimedOut

    def describe: String = this match
      case Crashed(e) =>
        val sw = java.io.StringWriter()
        e.printStackTrace(java.io.PrintWriter(sw))
        s"uncaught exception: ${sw.toString.linesIterator.take(12).mkString("\n")}"
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

  /** Exit code, stdout and stderr of one CLI invocation. */
  final case class Invocation(exit: Int, out: String, err: String)

  /** Runs `hugin <command> <file> <args>` on the program, written to a scratch file (always the same path,
   *  so that the output of two invocations can be compared). */
  def cli(command: String, program: Program, args: List[String] = Nil): Either[Failure, Invocation] =
    val file = scratch.resolve("fuzz.hgn")
    Files.writeString(file, program.code)
    val facts = program.facts.toList.flatMap { f =>
      val p = scratch.resolve("fuzz.facts")
      Files.writeString(p, f)
      List("--facts", p.toString)
    }
    guarded {
      val out = StringBuilder()
      val err = StringBuilder()
      val code = Main.run(List(command, file.toString, "--no-color") ++ facts ++ args, s => out ++= s += '\n', s => err ++= s += '\n')
      Invocation(code, out.toString, err.toString)
    }

  /** Diagnostics of a compilation, compiled in-process (to inspect their spans). */
  def diagnostics(code: String): Either[Failure, List[Diagnostic]] =
    guarded(Compiler.compile(SourceFile.virtual("fuzz.hgn", code), Settings(), _ => ()).reporter.diagnostics)

  /** Robustness properties of `check` and `run` (issue #7); the returned list of problems is empty if
   *  they hold. `check` must finish in time with exit code 0 or 1, deterministically, and report spans
   *  inside the file. `run --budget n` must not crash or exit with another code; with `mustRun`, a
   *  program accepted by `check` must also run to completion (a timeout is a problem), otherwise a run
   *  that exceeds the time limit is tolerated (a mutation may legitimately raise a bound to 2^63). */
  def robustness(program: Program, budget: Int, mustRun: Boolean): List[String] =
    def exitCode(what: String, i: Invocation) =
      Option.when(i.exit != 0 && i.exit != 1)(s"$what: exit code ${i.exit}\n${i.err}")
    cli("check", program) match
      case Left(f) => List(s"check: ${f.describe}")
      case Right(first) =>
        val again = cli("check", program) match
          case Left(f) => Some(s"second check: ${f.describe}")
          case Right(second) =>
            Option.when(second != first)(s"check is not deterministic:\n--- first\n${first.err}\n--- second\n${second.err}")
        val spans = diagnostics(program.code) match
          case Left(f) => List(s"compile: ${f.describe}")
          case Right(ds) =>
            for
              d <- ds
              s <- d.labels.map(_.span) ++ d.origin.frames.map(_.span)
              if s.exists && (s.start < 0 || s.end < s.start || s.end > s.source.content.length)
            yield s"diagnostic `${d.message}` has span ${s.start}..${s.end} outside the file (length ${s.source.content.length})"
        val run = cli("run", program, List("--budget", budget.toString)) match
          case Left(Failure.TimedOut) if !mustRun || first.exit != 0 => None
          case Left(f) => Some(s"run --budget $budget: ${f.describe}")
          case Right(r) =>
            exitCode("run", r).orElse(
              Option.when(mustRun && first.exit == 0 && r.exit != 0)(s"accepted by check, but run failed:\n${r.err}")
            )
        exitCode("check", first).toList ++ again ++ spans ++ run

/** A program with optional input facts, printed in full when a property fails. */
final case class Program(code: String, facts: Option[String] = None):
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
      Files.writeString(dir.resolve(s"$base.txt"), s"seed: ${Fuzz.seed}\n\n${problems.mkString("\n\n")}\n")
      problems.foldLeft(Prop.falsified)(_ :| _)
