package hugin.cli

import com.google.gson.{JsonParser, JsonElement}
import hugin.compiler.Settings
import hugin.lsp.Tokens
import hugin.query.{Compile, CompileKey, Database, Parse, SourceText}
import hugin.syntax.{Lexer, Tok}
import hugin.util.{Reporter, SourceFile}
import hugin.util.diagnostics.Json
import scala.collection.mutable
import scala.jdk.CollectionConverters.*
import scala.util.control.NonFatal

/** `hugin highlight` (internal; used by the build of the language reference, `reference/highlight.py`):
 *  the highlighting of code snippets, in one process for all of them.
 *
 *  stdin is a JSON array of snippets, each `{"code": "…", "prelude": true}` (`prelude` defaults to
 *  true); stdout is a JSON array with, per snippet, its text cut into runs `[text, [class, …]]` that
 *  cover it exactly. A run's classes are those of the language server's semantic tokens (the type of
 *  the token, then its modifiers, as in [[Tokens.types]] and [[Tokens.modifiers]]: the same tokens,
 *  computed by [[Tokens.tokens]]), and for the text they do not cover, lexical classes named like
 *  token types: `comment`, `string`, `number`, `keyword`, `operator`, `decorator` (directives),
 *  `variable`, `type` (the universe `Type`) and `label` (rule names `@r`). Plain text has no class.
 *
 *  A snippet that does not compile still gets its lexical classes and whatever semantic tokens the
 *  compiler's recovery yields. Snippets are compiled like the examples of the reference
 *  (`ReferenceExamplesSuite`): as a program of their own, with the prelude unless `prelude` is false,
 *  in one database, so the prelude and the standard library are elaborated once. */
object Highlight:
  final case class Snippet(code: String, prelude: Boolean = true)

  /** A run of a snippet's text and its classes (none: plain text). */
  final case class Run(text: String, classes: List[String])

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
    val semantic =
      try
        val index = db(Compile, CompileKey(Path, Settings(prelude = snippet.prelude))).index
        Tokens.tokens(index, source, Path).map(t => (t.span.start, t.span.end, t.typeName :: t.modifierNames))
      catch case NonFatal(_) => Nil // a compiler crash: the lexical classes only
    val covered = semantic.map((a, b, _) => (a, b))
    def free(a: Int, b: Int) = !covered.exists((c, d) => a < d && c < b)
    val classes = (semantic ++ lexical(source).filter((a, b, _) => free(a, b))).sortBy(_._1)
    val text = source.content
    val out = mutable.ListBuffer.empty[Run]
    var pos = 0
    for (a, b, cs) <- classes do
      if a > pos then out += Run(text.substring(pos, a), Nil)
      out += Run(text.substring(a, b), cs)
      pos = b
    if pos < text.length then out += Run(text.substring(pos), Nil)
    out.toList

  private val operators = Set(Tok.Turnstile, Tok.Query, Tok.Arrow, Tok.SubT, Tok.ColonColon)
  private val keywords =
    Set(Tok.KwType, Tok.KwRel, Tok.KwProp, Tok.KwNot, Tok.KwAs, Tok.KwWith, Tok.KwCount, Tok.KwSum, Tok.KwMin, Tok.KwMax, Tok.KwWhere)

  /** The lexical classes of a source, from its tokens; comments are the text between tokens that is not
   *  white space (the lexer skips them). */
  private def lexical(source: SourceFile): List[(Int, Int, List[String])] =
    val toks = Lexer(source, Reporter()).tokenize()
    val text = source.content
    val out = mutable.ListBuffer.empty[(Int, Int, List[String])]
    var prevEnd = 0
    for (t, i) <- toks.zipWithIndex do
      // the comments before the token
      var a = prevEnd
      var b = t.span.start
      while a < b && text.charAt(a).isWhitespace do a += 1
      while b > a && text.charAt(b - 1).isWhitespace do b -= 1
      if a < b then out += ((a, b, List("comment")))
      prevEnd = prevEnd.max(t.span.end)
      val cls = t.kind match
        case k if keywords(k) => Some("keyword")
        // `data` is a keyword only as the whole type of a declaration (`list A : data.`)
        case Tok.Name if t.text == "data" && toks.lift(i + 1).exists(_.kind == Tok.Period) => Some("keyword")
        case Tok.IntLit | Tok.FloatLit => Some("number")
        case Tok.StrLit => Some("string")
        case Tok.Directive => Some("decorator")
        case Tok.RuleName => Some("label")
        // the identifier `Type` names the universe of meta types (reference: lexical structure)
        case Tok.Var if t.text == "Type" => Some("type")
        case Tok.Var => Some("variable")
        case k if operators(k) => Some("operator")
        case _ => None
      cls.foreach(c => if t.span.end > t.span.start then out += ((t.span.start, t.span.end, List(c))))
    out.toList
