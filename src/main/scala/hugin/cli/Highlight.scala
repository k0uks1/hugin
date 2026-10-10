package hugin.cli

import com.google.gson.{JsonParser, JsonElement}
import hugin.compiler.Settings
import hugin.ide.Highlighting
import hugin.query.{Compile, CompileKey, Database, Parse, SourceText}
import hugin.util.diagnostics.Json
import scala.jdk.CollectionConverters.*
import scala.util.control.NonFatal

/** `hugin highlight` (internal; used by the build of the language reference, `reference/highlight.py`):
 *  the highlighting of code snippets, in one process for all of them.
 *
 *  stdin is a JSON array of snippets, each `{"code": "…", "prelude": true}` (`prelude` defaults to
 *  true); stdout is a JSON array with, per snippet, its text cut into runs `[text, [class, …]]` that
 *  cover it exactly. A run's classes are those of the language server's semantic tokens (the type of
 *  the token, then its modifiers, as in [[hugin.ide.Tokens.types]] and [[hugin.ide.Tokens.modifiers]]: the
 *  same tokens, computed by [[hugin.ide.Tokens.tokens]]), and for the text they do not cover, lexical
 *  classes named like token types: `comment`, `string`, `number`, `keyword`, `operator`, `decorator`
 *  (directives), `variable`, `type` (the universe `Type`) and `label` (rule names `@r`). Plain text has
 *  no class.
 *  The runs are computed by [[Highlighting.runs]], which the playground uses too.
 *
 *  A snippet that does not compile still gets its lexical classes and whatever semantic tokens the
 *  compiler's recovery yields. Snippets are compiled like the examples of the reference
 *  (`ReferenceExamplesSuite`): as a program of their own, with the prelude unless `prelude` is false,
 *  in one database, so the prelude and the standard library are elaborated once. */
object Highlight:
  final case class Snippet(code: String, prelude: Boolean = true)

  /** A run of a snippet's text and its classes (none: plain text). */
  type Run = Highlighting.Run
  val Run = Highlighting.Run

  /** The path of the snippet in the database (one at a time). */
  private val Path = "snippet.hgn"

  /** Reads the snippets, writes their runs; returns the exit code. */
  def main(in: java.io.InputStream, out: String => Unit, err: String => Unit): Int =
    val snippets =
      try Right(parse(String(in.readAllBytes(), java.nio.charset.StandardCharsets.UTF_8)))
      catch case NonFatal(e) => Left(e.getMessage)
    snippets match
      case Left(msg) =>
        err(s"error: `hugin highlight` expects a JSON array of {\"code\": …, \"prelude\": …} on stdin: $msg")
        ExitCode.Usage
      case Right(ss) =>
        given Database = Database()
        out(Json.Arr(ss.map(s => Json.Arr(runs(s).map(r => Json.Arr(List(Json.str(r.text), Json.Arr(r.classes.map(Json.str)))))))).render)
        ExitCode.Ok

  def parse(text: String): List[Snippet] =
    def field(o: com.google.gson.JsonObject, name: String): Option[JsonElement] = Option(o.get(name)).filterNot(_.isJsonNull)
    JsonParser.parseString(text).getAsJsonArray.asScala.toList.map { e =>
      val o = e.getAsJsonObject
      val code = field(o, "code").getOrElse(throw IllegalArgumentException("a snippet without \"code\"")).getAsString
      Snippet(code, field(o, "prelude").forall(_.getAsBoolean))
    }

  /** The runs of a snippet. */
  def runs(snippet: Snippet)(using db: Database): List[Run] =
    db.set(SourceText, Path, snippet.code)
    val source = db(Parse, Path).source
    Highlighting.runs(source, Path, db(Compile, CompileKey(Path, Settings(prelude = snippet.prelude))).index)
