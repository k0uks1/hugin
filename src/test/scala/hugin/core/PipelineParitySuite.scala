package hugin.core

import hugin.cli.Main

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** Acceptance test of redesign step B3 (docs/REDESIGN.md §10): every golden test program produces the
 *  same output (results, diagnostics, exit code) with `--new-meta` as with the old pipeline, except the
 *  programs listed in [[PipelineParitySuite.excluded]], each with the reason of the difference.
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
  /** Programs whose output differs, with the reason (REDESIGN §10, B3: diagnostics in the new meta
   *  level's words and concepts that changed). */
  val excluded: Map[String, String] = Map(
    "neg/a11_stage_overflow.hgn" -> "meta definitions are values: an overflow is reported where it reaches object code (E0909), not at the definition (E0209)",
    "neg/classification.hgn" -> "a relation-typed meta definition (`r : int -> rel = e.`) is allowed, so `= 5` is a type mismatch (E0901)",
    "neg/f_data_ctor_relation.hgn" -> "the label at the parameter's declaration is missing; relation types are printed without `⇑` inside the message",
    "neg/f_nil_ascription_help.hgn" -> "E0206 (a family's type argument not determined) has a generic help",
    "neg/interfaces.hgn" -> "signature mismatches in the new meta level's words (E0204 with the field, E0906 for a missing member)",
    "neg/meta_types.hgn" -> "meta type errors in the new meta level's words (E0204, E0901, E0905)",
    "neg/names.hgn" -> "meta definitions are elaborated in dependency order: a forward reference is fine (E0105 only for a self-reference)",
    "neg/polymorphic_recursion.hgn" -> "E0206 (a family's type argument not determined) has a generic help",
    "neg/stage.hgn" -> "stage errors of the new meta level (E0902); `not` over a formula function's expansion is E0202 `not a relation atom`",
    "neg/typedefs.hgn" -> "type definitions with parameters are meta functions, so they need not be strict (E0106 is retired)",
    "run/a10_meta_applicative.hgn" -> "the phase `monomorphize` is gone: the same object program is printed after `stage`",
    "run/f_demand_per_call.hgn" -> "the prelude of the new meta level is `<stdlib>/prelude-core.hgn` until B3c makes it the prelude (positions in it are the same)",
    "run/t_termination_explain.hgn" -> "the prelude of the new meta level is `<stdlib>/prelude-core.hgn` until B3c makes it the prelude (positions in it are the same)",
    "run/t_termination_len_callers.hgn" -> "the prelude of the new meta level is `<stdlib>/prelude-core.hgn` until B3c makes it the prelude (positions in it are the same)"
  )

/** A minimal line diff for the report. */
private object Diff:
  def unified(a: String, b: String): String =
    val (xs, ys) = (a.linesIterator.toVector, b.linesIterator.toVector)
    val removed = xs.diff(ys).map("- " + _)
    val added = ys.diff(xs).map("+ " + _)
    (removed ++ added).mkString("\n")
