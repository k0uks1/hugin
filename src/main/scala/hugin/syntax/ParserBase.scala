package hugin.syntax

import hugin.util.*
import scala.collection.mutable

/** The state of a parse shared by the parts of the grammar ([[ItemSyntax]], [[ExprSyntax]],
 *  [[RecordSyntax]], [[QuoteSyntax]], [[DirectiveSyntax]]): the token cursor, the `%infix` operators, error
 *  reporting and the recovery primitives (`docs/PARSER.md`, §4).
 *
 *  The parser is *resilient*: no parse function throws or gives up. A syntax error is reported once and
 *  becomes an error node ([[Trees.ErrorTree]]) or a piece taken as present (an inserted delimiter or
 *  period); the construct around it is built with what parsed. */
private[syntax] abstract class ParserBase(src: SourceFile, reporter: Reporter) extends TokenCursor(src, reporter):
  import Parser.*

  protected val infixOps = mutable.HashMap.empty[String, (Assoc, Int)]

  // ---------------------------------------------------------------- entry points of the parts

  def parseExpr(minLevel: Int): Tree
  protected def parsePostfix(): Tree
  protected def parseBraces(): Tree

  /** The item at the current token, and the declaration a prefix directive is attached to. */
  protected def parseItem(): List[Trees.Item]

  /** `item` with an error after it: its last part an error node (none for an item that cannot hold one). */
  protected def damagedItem(item: Trees.Item): Option[Trees.Item]

  // ---------------------------------------------------------------- types and non-types

  /** True while parsing a type: comparison operators (in particular `=`) end the type. */
  protected var inType = false

  /** An expression in a type (comparisons end it). */
  protected def parseType(minLevel: Int = LvlArrow): Tree = withType(true)(parseExpr(minLevel))

  protected def parseNonType(minLevel: Int): Tree = withType(false)(parseExpr(minLevel))

  private def withType[A](t: Boolean)(a: => A): A =
    val saved = inType
    inType = t
    try a
    finally inType = saved

  // ---------------------------------------------------------------- errors

  /** An error was reported in the current recovery region: further errors are not reported until the
   *  parser resynchronises ([[resync]]), so that one mistake gives one error (`docs/PARSER.md`, §4.2). */
  protected var quiet = false

  /** Reports a syntax error, unless one was reported in the current region. */
  protected def error(e: SyntaxError): Unit =
    if !quiet then reporter.report(e)
    quiet = true

  /** Reports an error that is not a matter of recovery (an invalid literal, `..` in an update): it is
   *  reported even in a region with an error, and does not silence the region. */
  protected def report(e: SyntaxError): Unit = reporter.report(e)

  /** The parser is in step with the text again (a new item, a separator or closing delimiter consumed). */
  protected def resync(): Unit = quiet = false

  /** Reports that one of `expected` was expected at the current token (unless it is a token of the lexer's
   *  errors, which are reported already), in the construct that started at `context`. */
  protected def expected(expected: List[Expect], context: Option[Context] = None, help: Option[SyntaxHelp] = None): Unit =
    if tok.kind == Tok.Error then quiet = true
    else error(SyntaxError.Expected(expected, found, tok.span, context.filter(c => c.start.startLine < tok.span.startLine), help))

  /** A missing expression: reported, and an error node at the insertion point; nothing is consumed (the
   *  token may be what an enclosing construct needs). A token of the lexer's errors is consumed. */
  protected def missing(what: Expect, context: Option[Context] = None): Tree =
    if tok.kind == Tok.Error then
      val t = advance()
      quiet = true
      ErrorTree(Nil)(t.span)
    else
      expected(List(what), context)
      ErrorTree(Nil)(Span(src, tok.span.start, tok.span.start))

  /** Consumes a token of kind `k` if it is there; otherwise reports it as expected and consumes nothing. */
  protected def expect(k: Tok, context: Option[Context] = None): Option[Token] =
    if at(k) then Some(advance())
    else
      expected(List(Expect.Token(k)), context)
      None

  // ---------------------------------------------------------------- delimiters

  /** Closes the delimiter `open` with `closer` (`docs/PARSER.md`, §4.3): consumes it if it is the current
   *  token; skips to it (with one error) if it follows within the current item; otherwise reports it as
   *  unclosed, with a suggestion inserting it, and continues as if it were there. False after an error:
   *  the construct is then an error node ([[damaged]]). */
  protected def close(open: Token, closer: Tok, context: Option[Context] = None): Boolean =
    val multiLine = openerEndsLine(open)
    if at(closer) && !strayCloserAt(open, closer, multiLine) then
      advance()
      true
    else
      val stray = at(closer)
      val ahead = if stray then closerAhead(closer, multiLine, i + 1) else closerAhead(closer, multiLine)
      if ahead >= 0 then
        if stray then error(SyntaxError.StrayCloser(tok.text, tok.span)) else expected(List(Expect.Token(closer)), context)
        while i < ahead do advance()
        advance()
        resync()
      else if tok.kind == Tok.Error then quiet = true
      else error(SyntaxError.Unclosed(open.text, open.span, Lexer.symbolText(closer), insertionPoint, found, tok.span))
      false

  /** `t` with a syntax error in or after it: an error node holding it. */
  protected def damaged(t: Tree): Tree = t match
    case e: ErrorTree => e
    case _ => ErrorTree(List(t))(t.span)

  /** `t`, or the error node holding it if `ok` is false. */
  protected def checked(t: Tree, ok: Boolean): Tree = if ok then t else damaged(t)

  // ---------------------------------------------------------------- items

  /** Ends the item (`context`) at its period (`docs/PARSER.md`, §4.1, §4.4): the period is consumed if it
   *  is there, and inserted if the item evidently ended (the next token starts a line or closes the
   *  enclosing body, or the file ends). Otherwise one of `expectations` was expected: reported, and the
   *  rest of the item is skipped. False after an error that makes the item uncertain: the caller then
   *  makes its last part an error node. An item with an inserted period is certain (and elaborated as
   *  usual) if it starts its line; one that starts after other text on its line (`a : rel. b`) may be
   *  a stray piece of text. */
  protected def endItem(context: Context, expectations: List[Expect]): Boolean =
    if at(Tok.Period) then
      advance()
      true
    else if tok.kind == Tok.Error then
      skipItem()
      false
    else if atBodyCloser && strayBodyCloser then
      // `same : t } -> rel.` in a body over several lines: the `}` is skipped with the rest of the item
      error(SyntaxError.StrayCloser(tok.text, tok.span))
      val stray = advance()
      // `s }.t`: the period is a selection, written after the stray `}`
      if at(Tok.Period) && tok.span.start == stray.span.end then advance()
      skipItem()
      false
    else if at(Tok.EOF) || startsLine(i) || atBodyCloser then
      val next = Option.when(tok.kind != Tok.EOF && !atBodyCloser)(tok.span)
      error(SyntaxError.MissingPeriod(context.construct, found, insertionPoint, next))
      firstOnLine(context.start)
    else
      expected(expectations, Some(context))
      skipItem()
      false

  /** Skips the rest of an item: to its period at depth 0 (consumed), or before a token in column 0, the `}`
   *  closing the enclosing body, or the end of the file. At the top level, a period followed by an
   *  indented line does not end the skip: top-level items start in column 0, so the indented text belongs
   *  to the damaged item (the members of a module body whose `{` was lost; issue #83). A token in column 0
   *  ends the skip also inside a delimiter opened in the skipped text, unless it closes one (`}` closing a
   *  body over several lines): a stray `{` does not take the rest of the file (`%use "f" {.`). `depth` is
   *  that of the skip's start, inside delimiters already skipped. Skipping junk between items
   *  (`directives`), a directive ends the skip: it starts the next item (`%use "a". : %use "b".`); in the
   *  rest of an item it is junk too (`f = %output '( … )`). */
  protected def skipItem(start: Int = 0, directives: Boolean = false): Unit =
    var depth = start
    var done = false
    def closing = kind == Tok.RParen || kind == Tok.RBrack || kind == Tok.RBrace
    while !done && !at(Tok.EOF) && !(atColumn0(i) && !at(Tok.Period) && (depth == 0 || !closing)) do
      kind match
        case Tok.LBrace | Tok.LParen | Tok.LBrack => depth += 1; advance()
        case Tok.RParen | Tok.RBrack | Tok.RBrace =>
          if depth == 0 && atBodyCloser then done = true else { depth = (depth - 1).max(0); advance() }
        case Tok.Period if depth == 0 =>
          advance()
          done = bodies > 0 || at(Tok.EOF) || !startsLine(i) || atColumn0(i)
        // a directive (other than the expressions `%import` and `%builtin`, and `%complete` of a signature)
        case Tok.Directive if directives && depth == 0 && startsDirectiveItem(tok) => done = true
        case _ => advance()

  /** The items of a file, a module body or a `where` block, while `more` holds: each item is a recovery
   *  region. A token that cannot start an item is reported by `unexpected` and skipped with the rest of
   *  its item (a period or `}` alone is skipped by itself, a `}` with a period right after it with that period). If it follows an item on the same line, that
   *  item's period may be the mistake (`go : nat . -> int.`): the item is damaged too (not for a second
   *  period, which is harmless). With whether no
   *  tokens were skipped (else a member may have been lost: the enclosing construct is damaged). */
  protected def parseItems(more: => Boolean, unexpected: Token => SyntaxError): (List[Trees.Item], Boolean) =
    val items = mutable.ListBuffer.empty[Trees.Item]
    var clean = true
    while more do
      resync()
      if startsItem(kind) then items ++= parseItem()
      else
        if items.nonEmpty && !startsLine(i) && !at(Tok.Period) && items.last.span.source.lineOf(
            (items.last.span.end - 1).max(items.last.span.start)
          ) == tok.span.startLine
        then
          val last = items.remove(items.length - 1)
          items ++= damagedItem(last)
        error(unexpected(tok))
        clean = false
        // a `{` at the end of its line opens a body over several lines, and one whose `}` follows within the
        // item a brace (`c. {mark N }.`): skipped with it, to its `}`
        val opensBody = at(Tok.LBrace) &&
          (toks(i + 1).kind != Tok.EOF && toks(i + 1).span.startLine > tok.span.startLine || closerAhead(Tok.RBrace, from = i + 1) >= 0)
        val t = advance()
        // a stray `}` directly followed by `.` closed an item whose opening was lost (a quote or module
        // body that ended early): the period is that item's end, not a mistake of its own (issue #83)
        if t.kind == Tok.RBrace && at(Tok.Period) && tok.span.startLine == t.span.startLine then advance()
        else if opensBody then skipItem(start = 1)
        else if t.kind != Tok.Period && t.kind != Tok.RBrace then skipItem(directives = true)
    (items.toList, clean)

object ParserBase:
  /** Looks at the current token without consuming one before the parser counts as stuck. */
  val Fuel = 1024
