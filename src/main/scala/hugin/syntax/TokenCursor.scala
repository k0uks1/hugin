package hugin.syntax

import hugin.util.*

/** The token cursor of the parser and the look-ahead that recovery decides by (`docs/PARSER.md`, §4.3,
 *  §4.4): the layout of lines and columns, the delimiters ahead and the bodies the parser is in. It reads
 *  tokens and reports nothing; [[ParserBase]] builds error reporting and recovery on it. */
private[syntax] abstract class TokenCursor(protected val src: SourceFile, protected val reporter: Reporter):
  protected val toks: Vector[Token] = QuoteOpeners.repair(Lexer(src, reporter).tokenize())
  protected var i = 0

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

  /** Whether the token at index `k` is the first of its line. */
  protected def startsLine(k: Int): Boolean = k > 0 && toks(k - 1).span.startLine < toks(k).span.startLine

  /** Whether the token at index `k` is the first of its line and in column 0: an argument cannot start
   *  there, and in recovery it is taken to start the next item (`docs/PARSER.md`, §4.4). */
  protected def atColumn0(k: Int): Boolean = toks(k).span.startCol == 0 && startsLine(k)

  /** Whether only white space precedes `span` on its line. */
  protected def firstOnLine(span: Span): Boolean =
    src.content.substring(src.lineStart(span.startLine), span.start).forall(_.isWhitespace)

  protected def found: Found = if tok.kind == Tok.EOF then Found.EndOfFile else Found.Token(tok.text)

  // ---------------------------------------------------------------- look-ahead

  /** Whether the opening delimiter `open` is the last token on its line: the construct is laid out over
   *  several lines, and its contents hold no end of an item. */
  protected def openerEndsLine(open: Token): Boolean =
    var j = i
    while j > 0 && toks(j - 1).span.start >= open.span.end do j -= 1
    j < toks.length && toks(j).kind != Tok.EOF && toks(j).span.startLine > open.span.startLine

  /** At `closer`: whether it is stray, in a construct laid out over several lines (`multiLine`: its opener
   *  ends its line) or one closed right after its opener. Such a construct is closed at the start of a
   *  line, at the indentation of the line of its opener; a closer that more of the construct follows on
   *  its line (`[`⏎`1,`⏎`2 ] 3`⏎`]`), or on the lines after it, indented (`{ }`⏎`a : t`⏎`}`), is stray if the
   *  next closer of its kind at depth 0 is laid out so. Not if an enclosing construct was opened on a line
   *  of that indentation: the later closer may then be the enclosing one's (`m = { k = h {`⏎`a = 1 } 2.`⏎`}.`). */
  protected def strayCloserAt(open: Token, closer: Tok, multiLine: Boolean): Boolean =
    val indent = indentation(open)
    val goesOn =
      if multiLine then !atColumn0(i) && continuesLine(i)
      else toks(i - 1).span.end == open.span.end && startsLine(i + 1) && toks(i + 1).kind != Tok.EOF && toks(i + 1).span.startCol > indent
    goesOn && {
      val k = closerAhead(closer, multiLine = true, from = i + 1)
      k >= 0 && startsLine(k) && toks(k).span.startCol == indent && !enclosingOpener(open).exists(indentation(_) == indent)
    }

  /** Whether more of a construct follows the token at index `k` on its line: a token other than a period,
   *  a separator or a closing delimiter, or a selection written after it (`}.t`, where the lexer sees a
   *  period, since a selector follows a name). */
  protected def continuesLine(k: Int): Boolean =
    def adjacent(a: Int) = a + 1 < toks.length && toks(a).span.end == toks(a + 1).span.start
    k + 1 < toks.length && toks(k + 1).span.startLine == toks(k).span.startLine && (toks(k + 1).kind match
      case Tok.Period => adjacent(k) && adjacent(k + 1) && toks(k + 2).kind == Tok.Name
      case Tok.Comma | Tok.Semi | Tok.RParen | Tok.RBrack | Tok.RBrace | Tok.EOF => false
      case _ => true
    )

  /** The indentation of the line of `t`. */
  protected def indentation(t: Token): Int =
    val start = src.lineStart(t.span.startLine)
    src.content.indexWhere(c => c != ' ' && c != '\t', start) - start

  /** The innermost opening delimiter not closed before `open` (of an enclosing construct or body), back to
   *  the first token in column 0 of a line. */
  private def enclosingOpener(open: Token): Option[Token] =
    var k = i - 1
    while k > 0 && toks(k).span.start > open.span.start do k -= 1
    var depth = 0
    var found = Option.empty[Token]
    var done = k <= 0 || atColumn0(k)
    while found.isEmpty && !done do
      k -= 1
      toks(k).kind match
        case Tok.RParen | Tok.RBrack | Tok.RBrace => depth += 1
        case Tok.LParen | Tok.LBrack | Tok.LBrace => if depth == 0 then found = Some(toks(k)) else depth -= 1
        case _ =>
      done = k <= 0 || atColumn0(k)
    found

  /** The index of `closer` at depth 0 ahead, within the current item: not past a period at depth 0 (any
   *  period, in a construct laid out over several lines), a token in column 0 or the end of the file; -1
   *  if there is none. The search starts at `from` (the current token by default). */
  protected def closerAhead(closer: Tok, multiLine: Boolean = false, from: Int = -1): Int =
    val start = if from < 0 then i else from
    var k = start
    var depth = 0
    while k < toks.length do
      val t = toks(k).kind
      // the closer itself may be in column 0 (`}` closing a body over several lines); any other token there
      // starts the next item
      if t == closer && depth == 0 && k > start then return k
      if t == Tok.EOF || (k > start && atColumn0(k)) then return -1
      t match
        case Tok.LParen | Tok.LBrack | Tok.LBrace => depth += 1
        case Tok.RParen | Tok.RBrack | Tok.RBrace =>
          // another closing delimiter at depth 0 is stray, or closes an enclosing construct, whose end
          // is then found by the period or the column-0 token after it
          if depth == 0 && t == closer then return k
          depth = (depth - 1).max(0)
        // a period ends the item, unless the closer follows on its line (a stray period: `{ X . | p X }`) or
        // what follows it cannot start an item (`{ a : t ., b : u }`, over several lines); in a construct
        // laid out over several lines, no period does: the construct ends with its closer
        case Tok.Period if depth == 0 && !multiLine && !closerOnLine(k + 1, closer) && endsItemAt(k + 1) => return -1
        case _ =>
      k += 1
    -1

  /** Whether a period before the token at index `k` can end an item: the token starts an item, starts a
   *  line, or is the end of the file. */
  protected def endsItemAt(k: Int): Boolean =
    k >= toks.length || toks(k).kind == Tok.EOF || startsLine(k) || startsItem(toks(k).kind)

  /** Whether `closer` follows at depth 0 on the line of the token at index `k`. */
  protected def closerOnLine(k: Int, closer: Tok): Boolean =
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

  /** The closers of the bodies the parser is in, innermost first: `}` for a module body, `)` for a
   *  reflection quote, whose entries are items too. Recovery inside an item stops at the innermost one. */
  protected var bodyClosers: List[Tok] = Nil

  protected def bodies: Int = bodyClosers.length

  /** At the closer of the innermost body. */
  protected def atBodyCloser: Boolean = bodyClosers.headOption.contains(kind)

  /** The `{` of each body the parser is in, as [[bodyClosers]]: none for a quote. */
  private var bodyOpeners: List[Option[Token]] = Nil

  /** Runs `f` inside a body closed by `closer`, opened by `open` (a module body's `{`). */
  protected def inBody[A](closer: Tok, open: Option[Token] = None)(f: => A): A =
    bodyClosers = closer :: bodyClosers
    bodyOpeners = open :: bodyOpeners
    try f
    finally
      bodyClosers = bodyClosers.tail
      bodyOpeners = bodyOpeners.tail

  /** At a `}` in the middle of an item of a module body laid out over several lines, which more of the item
   *  follows on its line (`same : t } -> rel.`): whether it is stray, the body being closed by the next `}`
   *  at depth 0, which starts a line at the indentation of the line of the body's `{`. In valid text a
   *  body's `}` follows the period of its last item. */
  protected def strayBodyCloser: Boolean =
    bodyOpeners.headOption.flatten.exists { open =>
      at(Tok.RBrace) && !startsLine(i) && toks(i - 1).kind != Tok.Period && continuesLine(i) && openerEndsLine(open) && {
        var k = i + 1
        var depth = 0
        while toks(k).kind != Tok.EOF && !(depth == 0 && toks(k).kind == Tok.RBrace) && !(atColumn0(k) && toks(k).kind != Tok.RBrace) do
          toks(k).kind match
            case Tok.LParen | Tok.LBrack | Tok.LBrace => depth += 1
            case Tok.RParen | Tok.RBrack | Tok.RBrace => depth -= 1
            case _ =>
          k += 1
        toks(k).kind == Tok.RBrace && startsLine(k) && toks(k).span.startCol == indentation(open)
      }
    }

  /** Whether a directive token starts an item: every directive but `%import` and `%builtin` (expressions)
   *  and `%complete` (a requirement in a signature). */
  protected def startsDirectiveItem(t: Token): Boolean =
    t.kind == Tok.Directive && t.text != "%import" && t.text != "%builtin" && t.text != "%complete"

  /** Whether a token can start an item (in recovery: whether skipping can stop before it). */
  protected def startsItem(t: Tok): Boolean = t match
    case Tok.Directive | Tok.Query | Tok.RuleName => true
    // `<t>` and `^A` are operands, never an item's head; nor is a brace (a record, a module body or implicit
    // binders), so a stray `{` is skipped instead of opening a body that swallows the next items
    case Tok.Lt | Tok.Caret | Tok.LBrace => false
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
