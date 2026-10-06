package hugin.compiler

/** Command-line settings that influence compilation. */
final case class Settings(
    color: Boolean = false,
    printAfter: Set[String] = Set.empty,
    stopAfter: Option[String] = None,
    budget: Option[Int] = None,
    facts: List[String] = Nil,
    warnings: Boolean = true,
    explainCodes: Boolean = false,
    /** Extra advisory checks (W0004). */
    lint: Boolean = false
)
