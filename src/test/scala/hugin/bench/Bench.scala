package hugin.bench

import hugin.cli.Main
import hugin.compiler.{Parsed, SourceLoader}
import hugin.core.{ProgramElab, SourceItems}
import hugin.util.SourceFile
import java.nio.file.Files

/** The benchmark harness of docs/PERFORMANCE.md (issue #60). Light by design: wall-clock medians of
 *  repeated runs in one JVM, after warm-up; the cold measurements (a new JVM per run) are taken by
 *  `bench/cold.sh` with the staged launcher.
 *
 *  {{{
 *  sbt "Test/runMain hugin.bench.Bench warm"        # prelude elaboration and the bench set, warm
 *  sbt "Test/runMain hugin.bench.Bench first"       # one compile of a one-line program in this JVM
 *  sbt "Test/runMain hugin.bench.Bench gen"         # (re)writes the generated bench programs
 *  }}}
 *
 *  `HUGIN_BENCH_RUNS` (default 15) sets the number of measured runs, `HUGIN_BENCH_WARMUP` (default 10)
 *  the warm-up runs. */
object Bench:
  private def env(name: String, default: Int): Int = sys.env.get(name).flatMap(_.toIntOption).getOrElse(default)
  private val runs = env("HUGIN_BENCH_RUNS", 15)
  private val warmup = env("HUGIN_BENCH_WARMUP", 10)

  def main(args: Array[String]): Unit = args.toList match
    case "gen" :: _ => BenchGen.writeAll()
    case "first" :: _ =>
      val t = time(compileOneLine())
      println(f"first compile of a one-line program in a new JVM: ${t / 1e6}%.1f ms")
    case "loop" :: what :: n :: _ =>
      // for profilers: repeats one measurement `n` times
      val f: () => Unit = what match
        case "prelude" => () => elabPrelude()
        case "one-line" => () => compileOneLine()
        case name => () => BenchSet.all.find(_.name.contains(name)).get.runInProcess()
      report(s"loop $what", f())
      for _ <- 0 until n.toInt do f()
    case "warm" :: only =>
      report("prelude elaboration (uncached, direct)", elabPrelude())
      report("compile one-line program (check, new database)", compileOneLine())
      for b <- BenchSet.all if only.isEmpty || only.exists(b.name.contains) do report(b.name, b.runInProcess())
    case _ => println("usage: Bench gen | first | warm [names...] | loop prelude|one-line|<name> <n>")

  /** The time of one call of `f`, in nanoseconds. */
  def time(f: => Unit): Long =
    val start = System.nanoTime()
    f
    System.nanoTime() - start

  def median(xs: Seq[Long]): Long =
    val s = xs.sorted
    if s.length % 2 == 1 then s(s.length / 2) else (s(s.length / 2 - 1) + s(s.length / 2)) / 2

  private def report(name: String, f: => Unit): Unit =
    for _ <- 0 until warmup do f
    val ts = (0 until runs).map(_ => time(f))
    println(f"$name%-60s median ${median(ts) / 1e6}%9.2f ms  (min ${ts.min / 1e6}%.2f, max ${ts.max / 1e6}%.2f, n=$runs)")

  /** Parses and elaborates the prelude directly, without any database or cache. */
  def elabPrelude(): Unit =
    val path = SourceLoader.PreludePath
    val parsed = Parsed(SourceFile.virtual(path, SourceLoader.stdlib(path).get))
    ProgramElab.prelude(SourceItems(path, "", parsed.program.items), builtinNames = true)

  private val oneLine = Files.createTempFile("hugin-bench-one", ".hgn")
  Files.writeString(oneLine, "p : int -> rel.\n")

  /** `hugin check` of a one-line program, in process (a new database, as the CLI does). */
  def compileOneLine(): Unit =
    val code = Main.run(List("check", oneLine.toString, "--no-color"), _ => (), _ => ())
    require(code == 0, "the one-line program does not compile")

/** One program of the bench set: a file, its facts files and the command (`check` or `run`). */
final case class BenchProgram(name: String, file: String, facts: List[String] = Nil, command: String = "run"):
  def args: List[String] = List(command, file) ++ facts.flatMap(f => List("--facts", f)) :+ "--no-color"

  def runInProcess(): Unit =
    val code = Main.run(args, _ => (), _ => ())
    require(code == 0, s"$name failed (exit code $code)")

/** The fixed bench set (docs/PERFORMANCE.md). */
object BenchSet:
  private def golden(name: String, facts: Boolean = false, command: String = "run"): BenchProgram =
    val f = s"tests/run/$name.hgn"
    BenchProgram(s"$command $name", f, if facts then List(s"tests/run/$name.facts") else Nil, command)

  val small: List[BenchProgram] = List(
    BenchProgram("check one-line", "bench/small/one.hgn", command = "check"),
    golden("a01_transitive_closure", facts = true),
    golden("a05_stratified"),
    golden("c1_aggregates")
  )

  val meta: List[BenchProgram] = List(
    golden("a04_typechecker", facts = true),
    golden("a10_meta_applicative"),
    golden("f_modules"),
    golden("c1_roundtrip"),
    golden("c2_module_wide"),
    BenchProgram("run meta_scaled", "bench/meta/meta_scaled.hgn")
  )

  val datalog: List[BenchProgram] = List(
    BenchProgram("run tc_chain", "bench/datalog/tc.hgn", List("bench/datalog/tc.facts")),
    BenchProgram("run shortest_grid", "bench/datalog/sp.hgn", List("bench/datalog/sp.facts")),
    BenchProgram("run strata", "bench/datalog/strata.hgn", List("bench/datalog/strata.facts"))
  )

  val large: List[BenchProgram] = List(
    BenchProgram("check gen_large", "bench/gen/large.hgn", command = "check"),
    BenchProgram("run gen_large", "bench/gen/large.hgn", List("bench/gen/large.facts"))
  )

  val all: List[BenchProgram] = small ++ meta ++ datalog ++ large

  /** For `bench/cold.sh`: one line per program, `name<TAB>args`. */
  def main(args: Array[String]): Unit = all.foreach(b => println(s"${b.name}\t${b.args.mkString(" ")}"))
