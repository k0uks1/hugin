package hugin.lsp

import com.google.gson.{JsonArray, JsonElement, JsonObject}
import hugin.compiler.MetaIndex.HintKind
import hugin.ide.{Expansions, Goals, Hints}
import hugin.query.{CompileKey, Database, Parse}
import hugin.util.{Diagnostic as HDiagnostic, SourceFile}
import org.eclipse.lsp4j.*
import org.eclipse.lsp4j.jsonrpc.messages.Either as JEither
import scala.jdk.CollectionConverters.*
import scala.util.Try

/** The client's settings of the inlay hints ([[hugin.ide.HintSettings]]). */
object HintSettings:
  /** The settings in a JSON object `{ "inlayHints": { "staging": …, … } }` (the client's initialization
   *  options, or its configuration under `hugin`); missing entries keep `current`'s. */
  def from(options: Any, current: hugin.ide.HintSettings): hugin.ide.HintSettings = options match
    case o: JsonObject =>
      val section = Option(o.get("hugin")).collect { case h: JsonObject => h }.getOrElse(o)
      Option(section.get("inlayHints")).collect { case h: JsonObject => h }.fold(current) { h =>
        def flag(name: String, default: Boolean) = Try(h.get(name).getAsBoolean).getOrElse(default)
        hugin.ide.HintSettings(flag("staging", current.staging), flag("implicits", current.implicits), flag("levels", current.levels))
      }
    case _ => current

/** The meta-level features of the server (issue #54) in terms of the protocol: inlay hints (initialization
 *  option and setting `inlayHints`), the structured data of typed holes, and the expansion lenses. What
 *  they answer is decided by [[hugin.ide]]: [[hugin.ide.Hints]], [[hugin.ide.Goals]],
 *  [[hugin.ide.Expansions]]; meta-level hover, completion and code actions are part of [[hugin.ide.Hover]],
 *  [[hugin.ide.Completion]] and [[hugin.ide.Fixes]]. */
final class MetaFeatures(using db: Database):
  var hintSettings: hugin.ide.HintSettings = hugin.ide.HintSettings()

  private def key(path: String) = CompileKey(path)
  private def source(path: String): SourceFile = db(Parse, path).source

  // ---------------------------------------------------------------------------------------- inlay hints

  def inlayHints(path: String, range: Range): List[InlayHint] =
    val src = source(path)
    val (from, to) = (Positions.offset(src, range.getStart), Positions.offset(src, range.getEnd))
    Hints.in(key(path), path, from, to, hintSettings).map { h =>
      val hint = InlayHint(Positions.position(h.at.source, h.at.start), JEither.forLeft(h.label))
      hint.setTooltip(JEither.forLeft[String, MarkupContent](h.tooltip))
      h.kind match
        case HintKind.Implicit =>
          hint.setKind(InlayHintKind.Type)
          hint.setPaddingLeft(true)
        case HintKind.Level => hint.setKind(InlayHintKind.Type)
        case HintKind.Staging =>
      hint
    }

  // -------------------------------------------------------------------------------------- typed holes

  /** The goal of a hole reported by `d` (E0924), as the LSP diagnostic's `data`: `{ "goal", "name",
   *  "stage", "context": [{ "name", "type" }] }`, from the compilation of the document at `path`. */
  def goalData(path: String, d: HDiagnostic): Option[JsonElement] =
    Goals.of(key(path), d).map { g =>
      val o = JsonObject()
      o.addProperty("goal", g.tpe)
      g.name.foreach(o.addProperty("name", _))
      o.addProperty("stage", g.stage)
      val ctx = JsonArray()
      for (x, t) <- g.context do
        val v = JsonObject()
        v.addProperty("name", x)
        v.addProperty("type", t)
        ctx.add(v)
      o.add("context", ctx)
      o
    }

  // ---------------------------------------------------------------------------------------- expansion

  /** A lens "Show expansion" on every directive or functor application of the file that produced object
   *  items; it runs the client command `hugin.showExpansion` with the URI and position, which asks the
   *  server for the text with the command [[MetaFeatures.ExpansionCommand]]. */
  def codeLenses(uri: String, path: String): List[CodeLens] =
    Expansions.sites(key(path), path).map { (span, n) =>
      val at = Positions.position(span.source, span.start)
      val args = List[Object](uri, Int.box(at.getLine), Int.box(at.getCharacter))
      CodeLens(
        Positions.range(span),
        Command(s"Show expansion (${if n == 1 then "1 item" else s"$n items"})", "hugin.showExpansion", args.asJava),
        null
      )
    }

object MetaFeatures:
  /** The command (`workspace/executeCommand`) that returns the expansion at a position, with the
   *  arguments `[uri, line, character]` (0-based) or `[{ "uri", "position" }]`: the text, or null. */
  val ExpansionCommand = "hugin.expansion"

  /** The URI and position of the arguments of [[ExpansionCommand]]. */
  def positionArgs(args: List[Any]): Option[(String, Position)] =
    def str(a: Any) = a match
      case p: com.google.gson.JsonPrimitive if p.isString => Some(p.getAsString)
      case s: String => Some(s)
      case _ => None
    def num(a: Any) = a match
      case p: com.google.gson.JsonPrimitive if p.isNumber => Some(p.getAsInt)
      case n: Number => Some(n.intValue)
      case _ => None
    args match
      case List(u, l, c) => for uri <- str(u); line <- num(l); char <- num(c) yield (uri, Position(line, char))
      case List(o: JsonObject) =>
        Try {
          val p = o.getAsJsonObject("position")
          (o.get("uri").getAsString, Position(p.get("line").getAsInt, p.get("character").getAsInt))
        }.toOption
      case _ => None
