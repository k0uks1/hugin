package hugin.compiler

import hugin.util.{Diagnostic, Severity}

/** Options that change what the compiler produces. They key the `Compile` query, so they must not include
 *  anything that only affects how results are shown (see [[Display]]). */
final case class Settings(
    /** Phases after which the program is printed (`all` for every phase). */
    printAfter: Set[String] = Set.empty,
    /** Phase after which compilation stops. */
    stopAfter: Option[String] = None,
    /** Auto-include the standard prelude (`<stdlib>/prelude.hgn`). */
    prelude: Boolean = true,
    /** Explain why every growing component terminates (`--explain-termination`). */
    explainTermination: Boolean = false,
    /** Elaborate with the new meta level (docs/REDESIGN.md, Phase B; hidden while it is developed). */
    newMeta: Boolean = false
)

/** How diagnostics are shown. Compilation always produces all diagnostics; clients filter and render
 *  them, so changing these options never recompiles. */
final case class Display(
    /** Render diagnostics with ANSI colours. */
    color: Boolean = false,
    /** Show warnings. */
    warnings: Boolean = true
):
  def shown(ds: List[Diagnostic]): List[Diagnostic] = if warnings then ds else ds.filter(_.severity != Severity.Warning)
