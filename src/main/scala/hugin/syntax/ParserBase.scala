package hugin.syntax

import hugin.util.*
import hugin.util.diagnostics.{Msg, msg}
import scala.language.implicitConversions
import scala.collection.mutable

/** The state of a parse shared by the parts of the grammar ([[ExprSyntax]], [[RecordSyntax]],
 *  [[QuoteSyntax]], [[DirectiveSyntax]], [[ItemSyntax]]): the token cursor, the `%infix` operators, error
 *  reporting and the entry points the parts call across each other. */
private[syntax] abstract class ParserBase(protected val src: SourceFile, protected val reporter: Reporter):
  import Parser.*

  protected val toks: Vector[Token] = Lexer(src, reporter).tokenize()
  protected var i = 0
  protected val infixOps = mutable.HashMap.empty[String, (Assoc, Int)]

  // ---------------------------------------------------------------- entry points of the parts

  def parseExpr(minLevel: Int): Tree
  protected def parsePostfix(): Tree
  protected def parseBraces(): Tree
  protected def parseItem(): Trees.Item
  protected def parseItemRecovering(): List[Trees.Item]

  // ---------------------------------------------------------------- the cursor

  protected def tok: Token = toks(i)
  protected def peekTok(k: Int): Token = toks((i + k).min(toks.length - 1))
  protected def kind: Tok = tok.kind
  protected def advance(): Token = { val t = tok; if i < toks.length - 1 then i += 1; t }
  protected def prevEnd: Int = if i == 0 then 0 else toks(i - 1).span.end
  protected def spanFrom(start: Int): Span = Span(src, start, prevEnd.max(start))
  protected def position: Int = i
  protected def tokenAt(k: Int): Token = toks(k.min(toks.length - 1))

  /** Whether `t` (the current token) is the first on its line and in column 0. */
  protected def atLineStart(t: Token): Boolean =
    t.span.startCol == 0 && i > 0 && toks(i - 1).span.startLine < t.span.startLine

  // ---------------------------------------------------------------- types and non-types

  /** True while parsing a type: comparison operators (in particular `=`) end the type. */
  protected var inType = false

  /** An expression in a type (comparisons end it). */
  protected def parseType(minLevel: Int = LvlArrow): Tree =
    val saved = inType
    inType = true
    try parseExpr(minLevel)
    finally inType = saved

  protected def parseNonType(minLevel: Int): Tree =
    val saved = inType
    inType = false
    try parseExpr(minLevel)
    finally inType = saved

  // ---------------------------------------------------------------- errors

  final class ParseError extends Exception(null, null, false, false)

  protected def report(e: SyntaxError): Unit = reporter.report(e)

  protected def fail(p: SyntaxError): Nothing =
    if kind == Tok.Error then throw new ParseError // already reported by the lexer
    reporter.report(p)
    throw new ParseError

  /** Reports that `what` was expected at the current token, and abandons the item. */
  protected def failExpected(what: Msg, label: Msg = Msg.empty, help: Option[Msg] = None): Nothing =
    fail(SyntaxError.Expected(what, found, tok.span, label, help))

  protected def found: Found =
    if kind == Tok.EOF then Found.EndOfFile else Found.Token(tok.text)

  /** Consumes a token of kind `k`, or reports that `what` was expected and abandons the item. */
  protected def expectTok(k: Tok, what: String = ""): Token =
    if kind == k then advance()
    else if kind == Tok.Error then throw new ParseError
    else
      val w = Msg.text(if what.nonEmpty then what else Lexer.describe(k))
      if k == Tok.Period && i > 0 && tok.span.startLine > toks(i - 1).span.startLine then
        // the item probably ends on the previous line
        val prev = toks(i - 1).span
        reporter.report(SyntaxError.MissingPeriod(w, found, Span(src, prev.end, prev.end), tok.span))
        // recover by accepting the item as if the period were present
        return Token(Tok.Period, ".", Span(src, prev.end, prev.end), false)
      failExpected(w, msg"expected $w")

  protected def expectPeriod(what: String): Unit = expectTok(Tok.Period, what)
