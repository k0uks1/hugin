package hugin.core

import hugin.cli.Main

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** Acceptance test of redesign step B3a (docs/REDESIGN.md §10): every golden test program that the new
 *  meta level can take over without modules, functors, families, formula functions or imports produces
 *  the same output (results, diagnostics, exit code) with `--new-meta` as with the old pipeline. The
 *  programs that are left out are listed in [[PipelineParitySuite.excluded]], each with its reason.
 *
 *  With `HUGIN_PARITY_REPORT=1`, the suite prints the differences of all programs (also the excluded
 *  ones) instead of failing. */
class PipelineParitySuite extends munit.FunSuite:
  import PipelineParitySuite.*

  private val report = sys.env.get("HUGIN_PARITY_REPORT").contains("1")

  private def files(dir: String): List[Path] =
    Files.list(Path.of("tests", dir)).iterator().asScala.filter(_.toString.endsWith(".hgn")).toList.sortBy(_.toString)

  private def sibling(p: Path, ext: String): Path =
    val name = p.toString
    Path.of(name.substring(0, name.lastIndexOf('.')) + ext)

  private def flags(p: Path): List[String] =
    val f = sibling(p, ".flags")
    if Files.exists(f) then Files.readString(f).trim.split("\\s+").filter(_.nonEmpty).toList else Nil

  private def run(args: List[String]): String =
    val out = new StringBuilder
    val code = Main.run(args :+ "--no-color", s => out ++= s += '\n', s => out ++= s += '\n')
    s"exit $code\n$out"

  private def command(p: Path, dir: String): List[String] =
    val facts = sibling(p, ".facts")
    val factArgs = if Files.exists(facts) then List("--facts", facts.toString) else Nil
    val verb = if dir == "neg" && factArgs.isEmpty then "check" else "run"
    (verb :: p.toString :: factArgs) ++ flags(p)

  private val programs =
    for
      dir <- List("run", "neg")
      p <- files(dir)
      if !flags(p).contains("--new-meta")
    yield (s"$dir/${p.getFileName}", p, dir)

  if report then
    test("report the differences between the pipelines") {
      for (name, p, dir) <- programs do
        val old = run(command(p, dir))
        val now = run(command(p, dir) :+ "--new-meta")
        if old != now then
          println(s"==== $name${excluded.get(name).fold("")(r => s" (excluded: $r)")}")
          println(Diff.unified(old, now))
    }
  else
    for (name, p, dir) <- programs if !excluded.contains(name) do
      test(name)(assertNoDiff(run(command(p, dir) :+ "--new-meta"), run(command(p, dir))))

object PipelineParitySuite:
  /** Programs outside the scope of B3a, with the reason. */
  val excluded: Map[String, String] = Map()

/** A minimal line diff for the report. */
private object Diff:
  def unified(a: String, b: String): String =
    val (xs, ys) = (a.linesIterator.toVector, b.linesIterator.toVector)
    val removed = xs.diff(ys).map("- " + _)
    val added = ys.diff(xs).map("+ " + _)
    (removed ++ added).mkString("\n")
