package hugin.cli

import com.google.gson.{JsonParser, JsonElement}
import hugin.compiler.Settings
import hugin.ide.{Annotations, Highlighting, Target}
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
 *  in one database, so the prelude and the standard library are elaborated once.
 *
 *  With `--info` (the reference's hovers, issue #132), each snippet's element is instead an object
 *  `{"runs": [[text, [class, …], name?], …], "names": [{"hover": h, "group": g, "decl": d, "target": t},
 *  …], "hovers": [[signature, note, …], …]}`: the snippet's annotation table ([[hugin.ide.Annotations]]).
 *  A run that is exactly a name has the name's index as its third element. A name's `hover` indexes the
 *  deduplicated `hovers` (null if hover shows nothing there); `group` numbers the occurrences of one
 *  symbol or object variable; `decl` is true at the declaration; `target` is the declaration's offset in
 *  the snippet (UTF-16 code units), or `[module, name]` for a declaration of the bundled standard library
 *  (`["std/graph", "tc"]`), and absent if there is none. A hover is its signature (null if it has none)
 *  followed by its notes. */
object Highlight:
  final case class Snippet(code: String, prelude: Boolean = true)

  /** A run of a snippet's text and its classes (none: plain text). */
  type Run = Highlighting.Run
  val Run = Highlighting.Run

  /** The path of the snippet in the database (one at a time). */
  private val Path = "snippet.hgn"

  /** Reads the snippets, writes their runs; returns the exit code. */
  def main(in: java.io.InputStream, out: String => Unit, err: String => Unit, info: Boolean = false): Int =
    val snippets =
      try Right(parse(String(in.readAllBytes(), java.nio.charset.StandardCharsets.UTF_8)))
      catch case NonFatal(e) => Left(e.getMessage)
    snippets match
      case Left(msg) =>
        err(s"error: `hugin highlight` expects a JSON array of {\"code\": …, \"prelude\": …} on stdin: $msg")
        ExitCode.Usage
      case Right(ss) =>
        given Database = Database()
        val json =
          if info then ss.map(s => infoJson(annotated(s)))
          else ss.map(s => Json.Arr(runs(s).map(r => Json.Arr(List(Json.str(r.text), Json.Arr(r.classes.map(Json.str)))))))
        out(Json.Arr(json).render)
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

  /** The runs of a snippet and its annotation table. */
  def annotated(snippet: Snippet)(using db: Database): (List[Run], Annotations) =
    val rs = runs(snippet)
    (rs, Annotations.of(CompileKey(Path, Settings(prelude = snippet.prelude)), Path))

  /** The output of `--info` for a snippet. */
  def infoJson(snippet: (List[Run], Annotations)): Json =
    val (rs, table) = snippet
    val byStart = table.names.zipWithIndex.map((n, i) => (n.span.start, n.span.end) -> i).toMap
    val offsets = rs.scanLeft(0)(_ + _.text.length)
    val runs = rs.zip(offsets).map { (r, start) =>
      val name = byStart.get((start, start + r.text.length)).map(i => Json.num(i.toLong))
      Json.Arr(List(Json.str(r.text), Json.Arr(r.classes.map(Json.str))) ++ name)
    }
    val names = table.names.map { n =>
      val target = n.target.collect {
        case Target.InFile(sp) if sp.source.path == Path => Json.num(sp.start.toLong)
        case Target.Library(module, name) => Json.Arr(List(Json.str(module), Json.str(name)))
      }
      Json.Obj(
        List(
          "hover" -> (if n.hover < 0 then Json.Null else Json.num(n.hover.toLong)),
          "group" -> Json.num(n.group.toLong),
          "decl" -> Json.Bool(n.declaration)
        ) ++ target.map("target" -> _)
      )
    }
    val hovers = table.hovers.toList.map(h => Json.Arr(h.signature.fold(Json.Null)(Json.str) :: h.notes.map(Json.str)))
    Json.obj("runs" -> Json.Arr(runs), "names" -> Json.Arr(names), "hovers" -> Json.Arr(hovers))
