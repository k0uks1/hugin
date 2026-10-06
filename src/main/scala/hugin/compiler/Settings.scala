package hugin.compiler

/** Settings that influence compilation. */
final case class Settings(
    /** Render diagnostics with ANSI colours. */
    color: Boolean = false,
    /** Phases after which the program is printed (`all` for every phase). */
    printAfter: Set[String] = Set.empty,
    /** Phase after which compilation stops. */
    stopAfter: Option[String] = None,
    /** Report warnings. */
    warnings: Boolean = true,
    /** Extra advisory checks (W0004). */
    lint: Boolean = false,
    /** Explain why every growing component terminates (`--explain-termination`). */
    explainTermination: Boolean = false
)
