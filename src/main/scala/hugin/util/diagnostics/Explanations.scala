package hugin.util.diagnostics

import java.nio.charset.StandardCharsets.UTF_8
import scala.util.Using

/** The long explanations of the codes: `docs/errors/<id>.md`, packaged as resources (see `build.sbt`). */
object Explanations:
  /** The URL of the published language reference, ending in `/`: `reference/site-url.txt`, packaged as the
   *  resource `/hugin/site-url.txt` (see `build.sbt`). */
  lazy val siteUrl: String =
    val in = Option(getClass.getResourceAsStream("/hugin/site-url.txt")).getOrElse(sys.error("resource /hugin/site-url.txt is missing"))
    val url = Using.resource(in)(s => String(s.readAllBytes(), UTF_8)).trim
    if url.endsWith("/") then url else url + "/"

  /** The Markdown explanation of a code, if one is packaged. */
  def markdown(code: Code): Option[String] =
    Option(getClass.getResourceAsStream(code.explanationResource)).map(in => Using.resource(in)(s => String(s.readAllBytes(), UTF_8)))

  /** The explanation as printed by `hugin explain` and `:explain`: the Markdown without the test
   *  attributes of its code blocks (` ```hugin fail=E0001 ` becomes ` ```hugin `). */
  def forTerminal(code: Code): Option[String] = markdown(code).map(_.replaceAll("(?m)^```(\\w+) .*$", "```$1").stripTrailing)

  /** The explanation of a code given by its id (case-insensitively), as printed by `hugin explain` and
   *  `:explain`: [[forTerminal]] followed by the link to its page in the error index. */
  def explain(id: String): Option[String] = Code.parse(id).flatMap(c => forTerminal(c).map(text => s"$text\n\nOnline: ${c.explanationUrl}"))

  /** The registry by phase, as printed by `hugin explain --list`. */
  def inventory: String =
    Code.byPhase
      .map { (phase, codes) =>
        val lines = codes.map(c => s"  ${c.id}  ${c.title}${c.lint.fold("")(l => s" (${l.name})")}${statusNote(c.status)}")
        (s"${phase.title}:" :: lines).mkString("\n")
      }
      .mkString("\n\n")

  private def statusNote(s: Status): String = s match
    case Status.Active => ""
    case Status.Retired(since) => s" [retired: $since]"
