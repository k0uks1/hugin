package hugin.compiler

import hugin.util.Diagnostic
import hugin.util.diagnostics.LintLevels

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
    /** Reject postulates `x : A = %postulate.` (`--safe`, E0925). */
    safe: Boolean = false,
    /** The meta constants whose assumptions (the postulates they depend on) are printed
     *  (`--print-assumptions`). */
    printAssumptions: List[String] = Nil,
    /** Record the instances of the rules for a proof export (`--export-proofs`, `hugin.runtime.ProofExport`). */
    exportProofs: Boolean = false,
    /** Certify the run (`--certify`, `hugin.runtime.Certify`): record the instances of the rules as for a
     *  proof export, and check them with `std/certify` after the run. */
    certify: Boolean = false
)

/** How diagnostics are shown. Compilation always produces all diagnostics; clients filter and render
 *  them, so changing these options never recompiles. */
final case class Display(
    /** Render diagnostics with ANSI colours. */
    color: Boolean = false,
    /** The levels of the lints (`-W`, `-A`, `-D`, `--deny-warnings`). */
    lints: LintLevels = LintLevels(),
    /** Print diagnostics as JSON lines (`--error-format=json`) instead of rendering them. */
    json: Boolean = false
):
  /** The diagnostics to show, with the lint levels applied (see [[LintLevels.apply]]). */
  def shown(ds: List[Diagnostic]): List[Diagnostic] = lints(ds)
