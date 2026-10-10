package hugin.ide

import hugin.compiler.SemanticIndex
import hugin.syntax.{Lexer, Tok}
import hugin.util.{Reporter, SourceFile}
import scala.collection.mutable
import scala.util.control.NonFatal

/** The highlighting of a program, as runs of its text with classes: those of the semantic tokens
 *  ([[Tokens.tokens]]: the token's type, then its modifiers) and, for the text they do not cover,
 *  lexical classes named like token types: `comment`, `string`, `number`, `keyword`, `operator`,
 *  `decorator` (directives), `variable`, `type` (the universe `Type`) and `label` (rule names `@r`).
 *  Plain text has no class. Used by `hugin highlight` (the reference and the landing page) and by the
 *  browser build (the playground). */
object Highlighting:
  /** A run of a program's text and its classes (none: plain text). */
  final case class Run(text: String, classes: List[String])

  /** The runs of `source` (the file `path`), with the semantic tokens of `index` (computed lazily; a
   *  failure, i.e. a compiler crash, leaves the lexical classes only). */
  def runs(source: SourceFile, path: String, index: => SemanticIndex): List[Run] =
    val semantic =
      try Tokens.tokens(index, source, path).map(t => (t.span.start, t.span.end, t.typeName :: t.modifierNames))
      catch case NonFatal(_) => Nil
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
        // the identifier `Type` names the universe of meta types (reference: meta/universes)
        case Tok.Var if t.text == "Type" => Some("type")
        case Tok.Var => Some("variable")
        case k if operators(k) => Some("operator")
        case _ => None
      cls.foreach(c => if t.span.end > t.span.start then out += ((t.span.start, t.span.end, List(c))))
    out.toList
