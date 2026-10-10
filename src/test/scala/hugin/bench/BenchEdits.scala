package hugin.bench

import hugin.compiler.Settings
import hugin.query.{Compile, CompileKey, Database, SourceText}
import java.nio.file.{Files, Path}

/** `Bench edits [names...]`: the latency of a compilation after an edit made as an editor makes it (issue
 *  #126, `docs/design/incrementality-2.md`, section 3). Each program is compiled once in a database; then
 *  each kind of edit is applied to the text, the program compiled again and the main thread's CPU time
 *  of that compilation measured (as `Bench cpu`), with the number of executions of the declarations
 *  (`signatures`) and of the object items (`elabItem`). Every repetition edits a different place, so
 *  that no memo of an earlier text is reused; the text is restored (unmeasured) after each.
 *
 *  - `from scratch`: a new database;
 *  - `edit a rule`: a one-line rule gets one more condition;
 *  - `type in a rule`: `_tmp` typed after a variable of a rule, one character at a time (every state is
 *    valid; the median per keystroke);
 *  - `edit a decl`: a declaration renamed; `add a decl`: a declaration added.
 *
 *  `HUGIN_BENCH_RUNS` (default 7) sets the repetitions, `HUGIN_BENCH_WARMUP` (default 2) the warm-up. */
object BenchEdits:
  private def env(name: String, default: Int): Int = sys.env.get(name).flatMap(_.toIntOption).getOrElse(default)
  private val runs = env("HUGIN_BENCH_RUNS", 7)
  private val warmup = env("HUGIN_BENCH_WARMUP", 2)

  val programs: List[(String, String)] = List(
    "typechecker" -> "examples/typechecker.hgn",
    "a04_typechecker" -> "tests/run/a04_typechecker.hgn",
    "c2_module_wide" -> "tests/run/c2_module_wide.hgn",
    "meta_scaled" -> "bench/meta/meta_scaled.hgn",
    "gen_large" -> "bench/gen/large.hgn"
  )

  private val mx = java.lang.management.ManagementFactory.getThreadMXBean

  /** One measurement: CPU time (ns) and executions of the declarations and of object items. */
  private final case class Sample(cpu: Long, signatures: Int, items: Int)

  def run(only: List[String]): Unit =
    for (name, file) <- programs if only.isEmpty || only.exists(name.contains) do
      val text = Files.readString(Path.of(file))
      val rules = text.linesIterator.zipWithIndex.collect {
        case (l, i) if l.contains(" :- ") && l.trim.endsWith(".") && !l.trim.startsWith("(*") && !l.startsWith(" ") => i
      }.toVector
      val lines = text.linesIterator.toVector
      def withLine(i: Int, l: String) = lines.updated(i, l).mkString("", "\n", "\n")
      def rule(k: Int) = rules((rules.length / 3 + 7 * k) % rules.length)
      val extra = "\nbench_decl : int -> rel.\n"
      val base = text + extra
      val edits: List[(String, Int => List[String])] = List(
        "edit a rule" -> (k => List(withLine(rule(k), lines(rule(k)).trim.stripSuffix(".") + s", $k = $k.") + extra)),
        "type in a rule" -> { k =>
          val l = lines(rule(k))
          val at =
            "[A-Z][A-Za-z0-9_]*".r.findFirstMatchIn(l.drop(l.indexOf(":-"))).map(m => l.indexOf(":-") + m.end).getOrElse(l.length - 1)
          (1 to 4).toList.map(n => withLine(rule(k), l.take(at) + "_tmp".take(n) + l.drop(at)) + extra)
        },
        "edit a decl" -> (k => List(text + extra.replace("bench_decl", s"bench_decl$k"))),
        "add a decl" -> (k => List(base + s"bench_added$k : int -> rel.\n"))
      )
      println(s"== $name ($file, ${lines.length} lines, ${rules.length} one-line rules)")
      val scratch = (0 until warmup + runs).map(_ => fresh(file, base)).drop(warmup)
      line("from scratch", scratch)
      val db = Database()
      db.set(SourceText, file, base)
      compile(db, file)
      for (label, texts) <- edits if rules.nonEmpty || !label.contains("rule") do
        val samples = (0 until warmup + runs).flatMap { k =>
          val measured = texts(k).map { t =>
            db.set(SourceText, file, t)
            measure(db, file)
          }
          db.set(SourceText, file, base)
          compile(db, file)
          if k < warmup then Nil else measured
        }
        line(label, samples)

  private def line(label: String, samples: Seq[Sample]): Unit =
    val ts = samples.map(_.cpu).sorted
    val median = ts(ts.length / 2)
    val sig = samples.map(_.signatures).sorted.apply(samples.length / 2)
    val items = samples.map(_.items).sorted.apply(samples.length / 2)
    println(f"  $label%-16s cpu median ${median / 1e6}%9.2f ms  (min ${ts.head / 1e6}%.2f)  signatures $sig, elabItem $items")

  private def settings = Settings()
  private def compile(db: Database, file: String): Unit = db(Compile, CompileKey(file, settings))

  private def measure(db: Database, file: String): Sample =
    db.stats.reset()
    val c0 = mx.getCurrentThreadCpuTime
    compile(db, file)
    val c1 = mx.getCurrentThreadCpuTime
    Sample(c1 - c0, db.stats.computedBy("signatures"), db.stats.computedBy("elabItem"))

  private def fresh(file: String, text: String): Sample =
    val db = Database()
    db.set(SourceText, file, text)
    measure(db, file)
