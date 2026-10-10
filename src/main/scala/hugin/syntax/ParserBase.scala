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
private[syntax] abstract class ParserBase(protected val src: SourceFile, protected val reporter: Reporter):
  import Parser.*

  protected val toks: Vector[Token] = Lexer(src, reporter).tokenize()
  protected var i = 0
  protected val infixOps = mutable.HashMap.empty[String, (Assoc, Int)]

  // ---------------------------------------------------------------- entry points of the parts

  def parseExpr(minLevel: Int): Tree
  protected def parsePostfix(): Tree
  protected def parseBraces(): Tree

  /** The item at the current token, and the declaration a prefix directive is attached to. */
  protected def parseItem(): List[Trees.Item]

  /** `item` with an error after it: its last part an error node (none for an item that cannot hold one). */
  protected def damagedItem(item: Trees.Item): Option[Trees.Item]

  // ---------------------------------------------------------------- the cursor

  /** Looks at the current token costs fuel, consuming one restores it: a loop that makes no progress
   *  runs out of fuel, which is a bug of the parser (matklad's resilient LL parsing). */
  private var fuel = ParserBase.Fuel

  protected def tok: Token = toks(i)
  protected def kind: Tok =
    fuel -= 1
    if fuel == 0 then throw IllegalStateException(s"the parser is stuck at ${tok.span.show}")
    toks(i).kind
  protected def at(k: Tok): Boolean = kind == k
  protected def peekTok(k: Int): Token = toks((i + k).min(toks.length - 1))
  protected def advance(): Token =
    fuel = ParserBase.Fuel
    val t = tok
    if i < toks.length - 1 then i += 1
    t
  protected def prevEnd: Int = if i == 0 then 0 else toks(i - 1).span.end
  protected def spanFrom(start: Int): Span = Span(src, start, prevEnd.max(start))
  protected def position: Int = i
  protected def tokenAt(k: Int): Token = toks(k.min(toks.length - 1))

  /** The empty span at the end of the previous token: where a missing token is inserted. */
  protected def insertionPoint: Span = Span(src, prevEnd, prevEnd)

  /** The line of each token and whether it starts in column 0, computed once per parse: the parser asks
   *  for them at every argument and recovery point, and `Span.startLine`/`startCol` search the line table
   *  each time (docs/PERFORMANCE.md, "The rest of #60"). */
  private lazy val tokenLines: Array[Int] =
    // `lineOf` of each start, by one walk over the line table: the tokens come in the order of the text
    val lines = new Array[Int](toks.length)
    var line = 0
    var previous = -1
    val it = toks.iterator
    var k = 0
    while it.hasNext do
      val sp = it.next().span
      val (file, start) = (sp.source, sp.start)
      if start < previous then line = file.lineOf(start)
      else while line + 1 < file.lineCount && file.lineStart(line + 1) <= start do line += 1
      lines(k) = line
      previous = start
      k += 1
    lines

  // a start is in column 0 exactly when it is its line's start (`startCol` counts the code points before it)
  private lazy val tokenInColumn0: Array[Boolean] =
    val lines = tokenLines
    val col0 = new Array[Boolean](toks.length)
    var k = 0
    for t <- toks do
      col0(k) = t.span.start == t.span.source.lineStart(lines(k))
      k += 1
    col0

  /** Whether the token at index `k` is the first of its line. */
  protected def startsLine(k: Int): Boolean = k > 0 && tokenLines(k - 1) < tokenLines(k)

  /** Whether the token at index `k` is the first of its line and in column 0: an argument cannot start
   *  there, and in recovery it is taken to start the next item (`docs/PARSER.md`, §4.4). */
  protected def atColumn0(k: Int): Boolean = tokenInColumn0(k) && startsLine(k)

  /** Whether only white space precedes `span` on its line. */
  protected def firstOnLine(span: Span): Boolean =
    src.content.substring(src.lineStart(span.startLine), span.start).forall(_.isWhitespace)

  protected def found: Found = if tok.kind == Tok.EOF then Found.EndOfFile else Found.Token(tok.text)

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
  private var quiet = false

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
    if at(closer) then
      advance()
      true
    else
      val ahead = closerAhead(closer)
      if ahead >= 0 then
        expected(List(Expect.Token(closer)), context)
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

  /** The index of `closer` at depth 0 ahead, within the current item: not past a period at depth 0, a token
   *  in column 0 or the end of the file; -1 if there is none. */
  private def closerAhead(closer: Tok): Int =
    var k = i
    var depth = 0
    while k < toks.length do
      val t = toks(k).kind
      // the closer itself may be in column 0 (`}` closing a body over several lines); any other token there
      // starts the next item
      if t == closer && depth == 0 && k > i then return k
      if t == Tok.EOF || (k > i && atColumn0(k)) then return -1
      t match
        case Tok.LParen | Tok.LBrack | Tok.LBrace => depth += 1
        case Tok.RParen | Tok.RBrack | Tok.RBrace =>
          // another closing delimiter at depth 0 is stray, or closes an enclosing construct, whose end
          // is then found by the period or the column-0 token after it
          if depth == 0 && t == closer then return k
          depth = (depth - 1).max(0)
        // a period ends the item, unless the closer follows on its line (a stray period: `{ X . | p X }`) or
        // what follows it cannot start an item (`{ a : t ., b : u }`, over several lines)
        case Tok.Period if depth == 0 && !closerOnLine(k + 1, closer) && endsItemAt(k + 1) => return -1
        case _ =>
      k += 1
    -1

  /** Whether a period before the token at index `k` can end an item: the token starts an item, starts a
   *  line, or is the end of the file. */
  private def endsItemAt(k: Int): Boolean =
    k >= toks.length || toks(k).kind == Tok.EOF || startsLine(k) || startsItem(toks(k).kind)

  /** Whether `closer` follows at depth 0 on the line of the token at index `k`. */
  private def closerOnLine(k: Int, closer: Tok): Boolean =
    val line = toks(k - 1).span.startLine
    var j = k
    var depth = 0
    while j < toks.length && toks(j).kind != Tok.EOF && toks(j).span.startLine == line do
      toks(j).kind match
        case Tok.LParen | Tok.LBrack | Tok.LBrace => depth += 1
        case t @ (Tok.RParen | Tok.RBrack | Tok.RBrace) =>
          if depth == 0 then return t == closer
          depth -= 1
        case _ =>
      j += 1
    false

  /** Whether `closer` closes the construct just opened somewhere ahead, before the end of its item (a
   *  period at depth 0) or of the file: a construct that is not closed and whose contents would start in
   *  column 0 of the next line is a stray opening delimiter at the end of a line. */
  protected def strayOpener(closer: Tok): Boolean =
    atColumn0(i) && {
      var k = i
      var depth = 0
      var closed = false
      var done = false
      while !done && k < toks.length do
        toks(k).kind match
          case Tok.EOF => done = true
          case Tok.LParen | Tok.LBrack | Tok.LBrace => depth += 1
          case t @ (Tok.RParen | Tok.RBrack | Tok.RBrace) =>
            if depth == 0 then { closed = t == closer; done = true }
            else depth -= 1
          case Tok.Period if depth == 0 => done = true
          case _ =>
        k += 1
      !closed
    }

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
    else if at(Tok.EOF) || startsLine(i) || atBodyCloser then
      val next = Option.when(tok.kind != Tok.EOF && !atBodyCloser)(tok.span)
      error(SyntaxError.MissingPeriod(context.construct, found, insertionPoint, next))
      firstOnLine(context.start)
    else
      expected(expectations, Some(context))
      skipItem()
      false

  /** The closers of the bodies the parser is in, innermost first: `}` for a module body, `)` for a
   *  reflection quote, whose entries are items too. Recovery inside an item stops at the innermost one. */
  protected var bodyClosers: List[Tok] = Nil

  protected def bodies: Int = bodyClosers.length

  /** At the closer of the innermost body. */
  protected def atBodyCloser: Boolean = bodyClosers.headOption.contains(kind)

  /** Runs `f` inside a body closed by `closer`. */
  protected def inBody[A](closer: Tok)(f: => A): A =
    bodyClosers = closer :: bodyClosers
    try f
    finally bodyClosers = bodyClosers.tail

  /** Skips the rest of an item: to its period at depth 0 (consumed), or before a token in column 0, the `}`
   *  closing the enclosing body, or the end of the file. At the top level, a period followed by an
   *  indented line does not end the skip: top-level items start in column 0, so the indented text belongs
   *  to the damaged item (the members of a module body whose `{` was lost; issue #83). */
  protected def skipItem(): Unit =
    var depth = 0
    var done = false
    while !done && !at(Tok.EOF) && !(atColumn0(i) && depth == 0 && !at(Tok.Period)) do
      kind match
        case Tok.LBrace | Tok.LParen | Tok.LBrack => depth += 1; advance()
        case Tok.RParen | Tok.RBrack | Tok.RBrace =>
          if depth == 0 && atBodyCloser then done = true else { depth = (depth - 1).max(0); advance() }
        case Tok.Period if depth == 0 =>
          advance()
          done = bodies > 0 || at(Tok.EOF) || !startsLine(i) || atColumn0(i)
        case _ => advance()

  /** Whether a token can start an item (in recovery: whether skipping can stop before it). */
  protected def startsItem(t: Tok): Boolean = t match
    case Tok.Directive | Tok.Query | Tok.RuleName => true
    // `<t>` and `^A` are operands, never an item's head
    case Tok.Lt | Tok.Caret => false
    case other => startsExpression(other)

  protected def startsExpression(t: Tok): Boolean = t match
    case Tok.Var | Tok.Name | Tok.IntLit | Tok.FloatLit | Tok.StrLit | Tok.LParen | Tok.LBrace | Tok.LBrack | Tok.Dollar | Tok.Up | Tok
          .Quote | Tok.Hole |
        Tok.KwNot | Tok.Minus | Tok.Lt | Tok.Caret | Tok.KwCount | Tok.KwSum | Tok.KwMin | Tok.KwMax | Tok.KwType | Tok.KwRel | Tok.KwProp |
        Tok.Directive | Tok.RuleName | Tok.Error =>
      true
    case _ => false

  /** Whether the current token starts a primary expression (as an argument of a directive). */
  protected def startsPrimary: Boolean =
    startsExpression(kind) && (tok.kind != Tok.Directive || tok.text == "%builtin" || tok.text == "%import")

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
        val t = advance()
        // a stray `}` directly followed by `.` closed an item whose opening was lost (a quote or module
        // body that ended early): the period is that item's end, not a mistake of its own (issue #83)
        if t.kind == Tok.RBrace && at(Tok.Period) && tok.span.startLine == t.span.startLine then advance()
        else if t.kind != Tok.Period && t.kind != Tok.RBrace then skipItem()
    (items.toList, clean)

object ParserBase:
  /** Looks at the current token without consuming one before the parser counts as stuck. */
  val Fuel = 1024
