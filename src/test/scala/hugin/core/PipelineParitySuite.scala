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
  val excluded: Map[String, String] = Map(
    "neg/a06_termination_nondecreasing.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "neg/a06_termination_unanchored.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "neg/a11_stage_overflow.hgn" -> "meta definitions are values: an overflow is reported where it reaches object code (E0909), not at the definition (E0209)",
    "neg/builtin.hgn" -> "diagnostics of the old meta typer, which the new meta level reports in its own words (updated in B3c)",
    "neg/classification.hgn" -> "`limit : int.` is a meta postulate and `f : int -> type` a meta function in the new meta level (REDESIGN §6.2), not misclassified object declarations",
    "neg/f_data_ctor_relation.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "neg/f_nil_ascription_help.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "neg/formula_modes.hgn" -> "formula functions: step B3b",
    "neg/import_paths.hgn" -> "imports: step B3b",
    "neg/imports.hgn" -> "imports: step B3b",
    "neg/interfaces.hgn" -> "modules, signatures or functors: step B3b",
    "neg/labels.hgn" -> "modules, signatures or functors: step B3b",
    "neg/lints.hgn" -> "formula functions: step B3b",
    "neg/meta_types.hgn" -> "modules, signatures or functors: step B3b",
    "neg/names.hgn" -> "diagnostics of the old meta typer, which the new meta level reports in its own words (updated in B3c); meta definitions may refer to later ones (no E0105)",
    "neg/negation_parameter.hgn" -> "modules, signatures or functors: step B3b",
    "neg/no_prelude.hgn" -> "base types are built into the new meta level (REDESIGN Q2), so they exist without the prelude",
    "neg/not_a_module.hgn" -> "modules, signatures or functors: step B3b",
    "neg/polymorphic_recursion.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "neg/refinements.hgn" -> "a cycle of refinements is reported as unresolved names (the new meta level elaborates declarations in dependency order)",
    "neg/requirements.hgn" -> "modules, signatures or functors: step B3b",
    "neg/stage.hgn" -> "formula functions: step B3b",
    "neg/typedefs.hgn" -> "a cycle of type definitions is reported as unresolved names; non-strict type definitions are families (B3b)",
    "run/a06_termination_len.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "run/a10_meta_applicative.hgn" -> "modules, signatures or functors: step B3b",
    "run/ex_formula_functions.hgn" -> "formula functions: step B3b",
    "run/ex_graphs.hgn" -> "modules, signatures or functors: step B3b",
    "run/ex_lists.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "run/f_absent_comparison.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "run/f_aggregate_disjunction.hgn" -> "formula functions: step B3b",
    "run/f_ctor_equations.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "run/f_demand_per_call.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "run/f_demand_per_call_disjunction.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "run/f_disjunction.hgn" -> "formula functions: step B3b",
    "run/f_fact_ctors.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "run/f_family_ctor_args.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "run/f_modules.hgn" -> "modules, signatures or functors: step B3b",
    "run/f_nil_comparison.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "run/f_struct_family.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "run/imports.hgn" -> "imports: step B3b",
    "run/interfaces.hgn" -> "modules, signatures or functors: step B3b",
    "run/n_repeated_vars.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "run/prelude_shadowing.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "run/t_termination_explain.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "run/t_termination_finite_ctors.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b",
    "run/t_termination_len_callers.hgn" -> "families of the prelude or the program (`list`, `option`, `pair`, `len`, …): memoised families are step B3b"
  )

/** A minimal line diff for the report. */
private object Diff:
  def unified(a: String, b: String): String =
    val (xs, ys) = (a.linesIterator.toVector, b.linesIterator.toVector)
    val removed = xs.diff(ys).map("- " + _)
    val added = ys.diff(xs).map("+ " + _)
    (removed ++ added).mkString("\n")
