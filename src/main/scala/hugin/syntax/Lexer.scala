package hugin.syntax

import hugin.util.*
import scala.collection.mutable

enum Tok:
  case Var, Name, RuleName, Directive, IntLit, FloatLit, StrLit
  // keywords
  case KwType, KwRel, KwProp, KwNot, KwAs, KwWith, KwCount, KwSum, KwMin, KwMax
  // symbols
  case Turnstile, Query, Arrow, SubT, Neq, Le, Ge, DotDot, Period, Select, Comma, Semi, Colon,
    Bar, Eq, Lt, Gt, Plus, Minus, Star, Slash, Caret, LParen, RParen, LBrace, RBrace, LBrack, RBrack
  // the meta level's `$` (splice, reference: meta/staging), `⇑` (lift) and `where`
  case Dollar, Up, KwWhere
  // `::`, the meta level's list constructor (reference: reflection)
  case ColonColon
  // `'` directly before `(`: the opener of a reflection quote `'( … )` (reference: reflection); the `(`
  // is a token of its own, so that delimiters nest as usual
  case Quote
  // `?` or `?name`: a typed hole of the meta level (reference: meta/functions)
  case Hole
  case EOF, Error

final case class Token(kind: Tok, text: String, span: Span, spaceBefore: Boolean):
  /** Literal payload for numbers/strings (already decoded). */
  var value: Any = null
  override def toString: String = s"$kind(${text})"

object Lexer:
  val keywords: Map[String, Tok] = Map(
    "type" -> Tok.KwType,
    "rel" -> Tok.KwRel,
    "prop" -> Tok.KwProp,
    "not" -> Tok.KwNot,
    "as" -> Tok.KwAs,
    "with" -> Tok.KwWith,
    "count" -> Tok.KwCount,
    "sum" -> Tok.KwSum,
    "min" -> Tok.KwMin,
    "max" -> Tok.KwMax
  )

  def describe(t: Tok): String = t match
    case Tok.Var => "a variable"
    case Tok.Name => "a name"
    case Tok.RuleName => "a rule name"
    case Tok.Directive => "a directive"
    case Tok.IntLit => "an integer"
    case Tok.FloatLit => "a float"
    case Tok.StrLit => "a string literal"
    case Tok.EOF => "end of file"
    case Tok.Period => "`.`"
    case Tok.Select => "a selector `.`"
    case Tok.Hole => "a hole `?`"
    case other => symbolText.getOrElse(other, other.toString.toLowerCase.stripPrefix("kw")) match
        case s => s"`$s`"

  val symbolText: Map[Tok, String] = Map(
    Tok.Turnstile -> ":-",
    Tok.Query -> "?-",
    Tok.Arrow -> "->",
    Tok.SubT -> "<:",
    Tok.Neq -> "<>",
    Tok.Le -> "<=",
    Tok.Ge -> ">=",
    Tok.DotDot -> "..",
    Tok.Comma -> ",",
    Tok.Semi -> ";",
    Tok.Colon -> ":",
    Tok.Bar -> "|",
    Tok.Eq -> "=",
    Tok.Lt -> "<",
    Tok.Gt -> ">",
    Tok.Plus -> "+",
    Tok.Minus -> "-",
    Tok.Star -> "*",
    Tok.Slash -> "/",
    Tok.Caret -> "^",
    Tok.LParen -> "(",
    Tok.RParen -> ")",
    Tok.LBrace -> "{",
    Tok.RBrace -> "}",
    Tok.LBrack -> "[",
    Tok.RBrack -> "]",
    Tok.Dollar -> "$",
    Tok.ColonColon -> "::",
    Tok.Quote -> "'(",
    Tok.Up -> "⇑",
    Tok.KwWhere -> "where",
    Tok.KwType -> "type",
    Tok.KwRel -> "rel",
    Tok.KwProp -> "prop",
    Tok.KwNot -> "not",
    Tok.KwAs -> "as",
    Tok.KwWith -> "with",
    Tok.KwCount -> "count",
    Tok.KwSum -> "sum",
    Tok.KwMin -> "min",
    Tok.KwMax -> "max"
  )

/** Hand-written lexer (Section 2.1). Errors are reported and lexing continues. */
final class Lexer(src: SourceFile, reporter: Reporter):
  private val s = src.content
  private var pos = 0
  private val out = mutable.ArrayBuffer.empty[Token]
  private var openComment = false

  /** Whether the text ended inside a comment (after [[tokenize]]); the REPL then reads more lines. */
  def unterminatedComment: Boolean = openComment

  private def span(a: Int, b: Int) = Span(src, a, b)
  private def err(p: Span => SyntaxError, a: Int, b: Int) = reporter.report(p(span(a, b)))

  private def peek(k: Int = 0): Char = if pos + k < s.length then s.charAt(pos + k) else '\u0000'
  private def isIdent(c: Char) = c.isLetterOrDigit && c < 128 || c == '_' || c == '\''

  def tokenize(): Vector[Token] =
    var space = true
    while
      val before = pos
      skipSpace()
      space = space || pos != before
      pos < s.length
    do
      val start = pos
      val prevEnd = if out.isEmpty then -1 else out.last.span.end
      val tok = lexOne(space)
      if tok != null then
        out += tok
      space = false
      if pos == start then pos += 1 // safety
    out += Token(Tok.EOF, "", span(s.length, s.length), true)
    out.toVector

  private def skipSpace(): Unit =
    var continue = true
    while continue && pos < s.length do
      val c = peek()
      if c.isWhitespace then pos += 1
      else if c == '(' && peek(1) == '*' then skipComment()
      else continue = false

  private def skipComment(): Unit =
    val start = pos
    var depth = 0
    var done = false
    while !done do
      if pos >= s.length then
        err(SyntaxError.UnterminatedComment(_), start, start + 2)
        openComment = true
        done = true
      else if peek() == '(' && peek(1) == '*' then { depth += 1; pos += 2 }
      else if peek() == '*' && peek(1) == ')' then
        depth -= 1; pos += 2
        if depth == 0 then done = true
      else pos += 1

  private def mk(kind: Tok, start: Int, space: Boolean): Token =
    Token(kind, s.substring(start, pos), span(start, pos), space)

  private def lexOne(space: Boolean): Token =
    val start = pos
    val c = peek()
    if c.isLetter && c < 128 || c == '_' then
      while isIdent(peek()) do pos += 1
      val text = s.substring(start, pos)
      if c.isUpper || c == '_' then mk(Tok.Var, start, space)
      else if text == "where" then mk(Tok.KwWhere, start, space)
      else
        Lexer.keywords.get(text) match
          case Some(kw) => mk(kw, start, space)
          case None => mk(Tok.Name, start, space)
    else if c.isDigit then lexNumber(start, space)
    else if c == '"' then lexString(start, space)
    else if c == '@' || c == '%' then
      pos += 1
      if peek().isLetter && peek().isLower then
        while isIdent(peek()) do pos += 1
        mk(if c == '@' then Tok.RuleName else Tok.Directive, start, space)
      else
        err(SyntaxError.NameExpectedAfter(c, _), start, pos)
        null
    else
      def sym(k: Tok, n: Int): Token = { pos += n; mk(k, start, space) }
      c match
        case ':' if peek(1) == '-' => sym(Tok.Turnstile, 2)
        case ':' if peek(1) == ':' => sym(Tok.ColonColon, 2)
        case ':' => sym(Tok.Colon, 1)
        case '?' if peek(1) == '-' => sym(Tok.Query, 2)
        case '?' =>
          // a hole, named by the identifier directly after it
          pos += 1
          while isIdent(peek()) do pos += 1
          mk(Tok.Hole, start, space)
        case '-' if peek(1) == '>' => sym(Tok.Arrow, 2)
        case '-' => sym(Tok.Minus, 1)
        case '<' if peek(1) == ':' => sym(Tok.SubT, 2)
        case '<' if peek(1) == '>' => sym(Tok.Neq, 2)
        case '<' if peek(1) == '=' => sym(Tok.Le, 2)
        case '<' => sym(Tok.Lt, 1)
        case '>' if peek(1) == '=' => sym(Tok.Ge, 2)
        case '>' => sym(Tok.Gt, 1)
        case '.' if peek(1) == '.' => sym(Tok.DotDot, 2)
        case '.' =>
          // selector iff immediately preceded by an identifier, a variable or `)` and followed by a lowercase
          // identifier: `g.edge`, `(r).a`
          val prevIdent = !space && out.nonEmpty && out.last.span.end == start &&
            (out.last.kind == Tok.Var || out.last.kind == Tok.Name || out.last.kind == Tok.RParen)
          val nextLower = peek(1).isLetter && peek(1).isLower && peek(1) < 128
          if prevIdent && nextLower then sym(Tok.Select, 1) else sym(Tok.Period, 1)
        case ',' => sym(Tok.Comma, 1)
        case ';' => sym(Tok.Semi, 1)
        case '|' => sym(Tok.Bar, 1)
        case '=' => sym(Tok.Eq, 1)
        case '+' => sym(Tok.Plus, 1)
        case '*' => sym(Tok.Star, 1)
        case '/' => sym(Tok.Slash, 1)
        case '^' => sym(Tok.Caret, 1)
        case '(' => sym(Tok.LParen, 1)
        case ')' => sym(Tok.RParen, 1)
        case '{' => sym(Tok.LBrace, 1)
        case '}' => sym(Tok.RBrace, 1)
        case '[' => sym(Tok.LBrack, 1)
        case ']' => sym(Tok.RBrack, 1)
        case '$' => sym(Tok.Dollar, 1)
        // a prime is an identifier character (`x'`); at the start of a token, before `{`, it opens a quote
        case '\'' if peek(1) == '(' => sym(Tok.Quote, 1)
        case '⇑' => sym(Tok.Up, 1)
        case _ =>
          val cp = s.codePointAt(pos)
          pos += Character.charCount(cp)
          err(SyntaxError.UnexpectedCharacter(new String(Character.toChars(cp)), _), start, pos)
          null

  private def lexNumber(start: Int, space: Boolean): Token =
    while peek().isDigit do pos += 1
    var isFloat = false
    if peek() == '.' && peek(1).isDigit then
      isFloat = true
      pos += 1
      while peek().isDigit do pos += 1
      if (peek() == 'e' || peek() == 'E') && (peek(1).isDigit || ((peek(1) == '+' || peek(1) == '-') && peek(2).isDigit)) then
        pos += 2
        while peek().isDigit do pos += 1
    val text = s.substring(start, pos)
    if isFloat then
      val t = mk(Tok.FloatLit, start, space)
      t.value = text.toDouble
      t
    else
      val t = mk(Tok.IntLit, start, space)
      t.value =
        try java.lang.Long.parseLong(text)
        catch
          case _: NumberFormatException =>
            // -9223372036854775808 is written as unary minus applied to an out-of-range literal; keep BigInt for the parser
            BigInt(text)
      t

  private def lexString(start: Int, space: Boolean): Token =
    pos += 1
    val sb = new StringBuilder
    var done = false
    var bad = false
    while !done do
      if pos >= s.length || peek() == '\n' then
        err(SyntaxError.UnterminatedString(_), start, pos)
        done = true
        bad = true
      else
        val c = peek()
        if c == '"' then { pos += 1; done = true }
        else if c == '\\' then
          val escStart = pos
          pos += 1
          peek() match
            case '"' => sb += '"'; pos += 1
            case '\\' => sb += '\\'; pos += 1
            case 'n' => sb += '\n'; pos += 1
            case 't' => sb += '\t'; pos += 1
            case 'u' if peek(1) == '{' =>
              pos += 2
              val hs = pos
              while peek().isLetterOrDigit do pos += 1
              val hex = s.substring(hs, pos)
              if peek() == '}' then pos += 1
              try
                val cp = Integer.parseInt(hex, 16)
                if cp < 0 || cp > 0x10ffff || (cp >= 0xd800 && cp <= 0xdfff) then throw new NumberFormatException
                sb.appendAll(Character.toChars(cp))
              catch
                case _: NumberFormatException =>
                  err(SyntaxError.InvalidUnicodeEscape(hex, _), escStart, pos)
            case _ if pos >= s.length => // `\` at the end of the input: the string is unterminated
            case _ =>
              pos += 1
              err(SyntaxError.InvalidEscape(_), escStart, pos)
        else
          sb += c; pos += 1
    if bad then return mk(Tok.Error, start, space)
    val t = mk(Tok.StrLit, start, space)
    t.value = sb.toString
    t
