package hugin.util.diagnostics

import hugin.util.Severity

/** The phase a code belongs to. Error codes are numbered in blocks of a hundred per phase ([[block]]), so
 *  that a number hints at the phase; lints (`W` codes) are numbered on their own. */
enum Phase(val title: String, val block: Int):
  case Syntax extends Phase("syntax", 0)
  case Names extends Phase("names and imports", 1)
  case MetaTyping extends Phase("stage and meta typing", 2)
  case Records extends Phase("records", 3)
  case ObjectTyping extends Phase("object typing", 4)
  case Moding extends Phase("moding", 5)
  case Checks extends Phase("checks", 6)
  case Directives extends Phase("directives", 7)
  case Input extends Phase("input facts", 8)

  /** Diagnostics that user-defined directives report (redesign C2). The block E0900–E0999 is reserved for
   *  them; they are reported through the same [[Problem]] API as the compiler's own. */
  case UserDirectives extends Phase("user directives", 9)
  case Lints extends Phase("lints", -1)

/** The default level of a code. Lints may be re-levelled from the command line once lint flags exist. */
enum Level:
  case Error, Warning, Allow

  def severity: Severity = this match
    case Error => Severity.Error
    case Warning | Allow => Severity.Warning

enum Status:
  case Active

  /** No longer emitted. A retired code is never removed and its number never reused. */
  case Retired(since: String)

/** A diagnostic code: the registry of every code Hugin has ever emitted. Append-only; numbers keep their
 *  meaning forever. One code names one *concept* (one explanation), so several problem cases may share
 *  a code, but a code is never an umbrella for unrelated causes.
 *
 *  To add a code: append a case with the next free number in its phase's block, add a negative golden
 *  test in `tests/neg` that produces it, and (from M2 on) an explanation `docs/errors/<id>.md`. */
enum Code(
    val number: Int,
    val phase: Phase,
    val title: String,
    val level: Level = Level.Error,
    /** The lint name of a warning (`singleton_variables`), used by lint flags. */
    val lint: Option[String] = None,
    /** Shown faded by editors (LSP `DiagnosticTag.Unnecessary`). */
    val unnecessary: Boolean = false,
    val status: Status = Status.Active
):
  // syntax
  case E0001 extends Code(1, Phase.Syntax, "syntax error")
  case E0002 extends Code(2, Phase.Syntax, "unterminated comment or string")
  case E0003 extends Code(3, Phase.Syntax, "invalid literal")
  case E0004 extends Code(4, Phase.Syntax, "malformed item")
  // names and imports
  case E0101 extends Code(101, Phase.Names, "unresolved name")
  case E0102 extends Code(102, Phase.Names, "duplicate declaration")
  case E0103 extends Code(103, Phase.Names, "misclassified item")
  case E0104 extends Code(104, Phase.Names, "cyclic type definition")
  case E0105 extends Code(105, Phase.Names, "forward reference")
  case E0106 extends Code(106, Phase.Names, "non-strict type definition")
  case E0107 extends Code(107, Phase.Names, "not a module")
  case E0108 extends Code(108, Phase.Names, "import error")
  // stage and meta typing
  case E0201 extends Code(201, Phase.MetaTyping, "runtime value used at compile time")
  case E0202 extends Code(202, Phase.MetaTyping, "stage error")
  case E0203 extends Code(203, Phase.MetaTyping, "meta type mismatch")
  case E0204 extends Code(204, Phase.MetaTyping, "signature mismatch")
  case E0205 extends Code(205, Phase.MetaTyping, "polymorphic recursion")
  case E0206 extends Code(206, Phase.MetaTyping, "cannot infer type argument")
  case E0207 extends Code(207, Phase.MetaTyping, "arity mismatch")
  case E0208 extends Code(208, Phase.MetaTyping, "unsatisfied requirement")
  case E0209 extends Code(209, Phase.MetaTyping, "compile-time arithmetic failure")
  case E0210 extends Code(210, Phase.MetaTyping, "negation over a parameter without %complete")
  // records
  case E0301 extends Code(301, Phase.Records, "missing labels in named pattern")
  case E0302 extends Code(302, Phase.Records, "`..` in a head")
  case E0303 extends Code(303, Phase.Records, "projection on a type that is not closed")
  case E0304 extends Code(304, Phase.Records, "no common label")
  case E0305 extends Code(305, Phase.Records, "undefined join")
  case E0306 extends Code(306, Phase.Records, "unknown label")
  case E0307 extends Code(307, Phase.Records, "duplicate label")
  // object typing
  case E0401 extends Code(401, Phase.ObjectTyping, "no value can occur in all these positions")
  case E0402 extends Code(402, Phase.ObjectTyping, "type mismatch")
  case E0404 extends Code(404, Phase.ObjectTyping, "ill-formed declaration")
  case E0405 extends Code(405, Phase.ObjectTyping, "invalid ascription")
  case E0406 extends Code(406, Phase.ObjectTyping, "data constructor used as a relation")
  // moding
  case E0501 extends Code(501, Phase.Moding, "unbound variable")
  case E0502 extends Code(502, Phase.Moding, "call without applicable mode")
  case E0503 extends Code(503, Phase.Moding, "input position is not a pattern")
  case E0504 extends Code(504, Phase.Moding, "fact constructor built in a moded input")
  // checks
  case E0601 extends Code(601, Phase.Checks, "stratification cycle through negation")
  case E0602 extends Code(602, Phase.Checks, "negation or aggregation over an incomplete relation")
  case E0603 extends Code(603, Phase.Checks, "growing component without valid %terminates")
  case E0604 extends Code(604, Phase.Checks, "invalid %terminates directive")
  // directives
  case E0701 extends Code(701, Phase.Directives, "invalid directive")
  // input facts
  case E0801 extends Code(801, Phase.Input, "invalid input fact")
  // lints
  case W0001
      extends Code(1, Phase.Lints, "undefined constant expression", Level.Warning, lint = Some("undefined_constant_expressions"))
  case W0002
      extends Code(2, Phase.Lints, "singleton variable", Level.Warning, lint = Some("singleton_variables"), unnecessary = true)
  case W0003 extends Code(3, Phase.Lints, "unused definition", Level.Warning, lint = Some("unused_definitions"), unnecessary = true)
  case W0005
      extends Code(5, Phase.Lints, "formula function without clauses", Level.Warning, lint = Some("empty_formula_functions"))

  /** The code as users see it: `E0602`, `W0002`. */
  def id: String = (if lint.isDefined then "W" else "E") + f"$number%04d"

  def isActive: Boolean = status == Status.Active

  /** The explanation, packaged as a resource (from `docs/errors/<id>.md`). */
  def explanationResource: String = s"/hugin/errors/$id.md"

  /** The explanation's path in the repository (used as a link by JSON output and the LSP). */
  def explanationPath: String = s"docs/errors/$id.md"

object Code:
  /** The codes reserved for diagnostics reported by user-defined directives (see [[Phase.UserDirectives]]). */
  val userDirectiveNumbers: Range = 900 until 1000

  /** A code by its id, case-insensitively. */
  def parse(s: String): Option[Code] = values.find(_.id.equalsIgnoreCase(s.trim))

  /** The registry grouped by phase, in phase order. */
  def byPhase: List[(Phase, List[Code])] =
    Phase.values.toList.map(p => p -> values.toList.filter(_.phase == p)).filter(_._2.nonEmpty)
