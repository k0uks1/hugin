package hugin.syntax

import scala.collection.mutable

/** The grammar of reflection (reference: reflection), mixed into [[Parser]]:
 *
 *  - quotes `'( … )`: object syntax as data. The content is a sequence of entries as in a file, separated
 *    by periods (the last period optional): `[@name] e [:- b]` (a rule, or a fact whose head `e` is kept
 *    whole: a formula, a term, a measure) and `?- b` (a query). The expected type chooses the category;
 *  - holes `$x`, sequence holes `$..xs` and higher-order holes `$f[t̄]` (the `[` directly after `f`), which
 *    the elaborator accepts only inside a quote (outside, `$x` is the staging splice);
 *  - meta lists `[]`, `[e₁, …, eₙ]` and `e :: es`. A `[` starts a list unless it has the shape of a
 *    lambda `[x] e` (one name, optionally typed, followed by an expression).
 */
private[syntax] trait QuoteSyntax extends ParserBase:
  /** `'( … )`, at `'`. An unclosed quote is E0005 (the `'(` never closed); the entries are recovery
   *  regions, like the items of a module body, and like them they do not start in column 0 (a quote over
   *  several lines indents its entries), so that an unclosed quote ends before the next item. */
  protected def parseQuote(): Tree =
    val q = advance()
    val paren = advance()
    val open = Token(Tok.LParen, "'(", q.span.to(paren.span), q.spaceBefore)
    val entries = mutable.ListBuffer.empty[Trees.Item]
    var terminated = false
    var more = !at(Tok.RParen) && startsEntry && !atColumn0(position)
    var periods = 0
    // the quote is a body: recovery inside an entry stops at the quote's `)` instead of skipping past it
    inBody(Tok.RParen) {
      while more do
        entries += parseEntry()
        terminated = at(Tok.Period)
        if terminated then
          periods += 1
          advance()
          resync()
        else if periods > 0 && strayCloser then
          // `N = ) count { … }.` in a quote of several entries (a module): a `)` in the middle of an entry,
          // with the entry going on after it on the same line, is a stray token, not the end of the quote
          // (in a one-entry quote `f '( X ) Y` the `)` may well end it)
          expected(List(Expect.period))
          advance()
          skipItem()
          terminated = toks(position - 1).kind == Tok.Period
          resync()
        else if !at(Tok.RParen) && !at(Tok.EOF) && !atColumn0(position) then
          // a damaged entry: skip to its period (or to the quote's `)`) and go on with the next entry
          expected(List(Expect.period))
          skipItem()
          terminated = toks(position - 1).kind == Tok.Period
          resync()
        // as in a module body, an entry does not start in column 0: an unclosed quote ends before it
        more = terminated && !at(Tok.RParen) && startsEntry && !atColumn0(position)
    }
    val closed = close(open, Tok.RParen)
    checked(Trees.Quote(entries.toList, terminated)(spanFrom(q.span.start)), closed)

  private def startsEntry: Boolean = kind == Tok.Query || startsExpression(kind)

  /** At a `)` that an unterminated entry ran into: whether the entry continues after it on the same line
   *  (anything but the end of the item, `.`, `,` or another closer), so that the `)` is stray. */
  private def strayCloser: Boolean =
    at(Tok.RParen) && position + 1 < toks.length && {
      val next = toks(position + 1)
      next.span.startLine == tok.span.startLine && (next.kind match
        case Tok.Period | Tok.Comma | Tok.RParen | Tok.RBrack | Tok.RBrace | Tok.EOF => false
        case _ => true
      )
    }

  private def parseEntry(): Trees.Item =
    val start = tok.span.start
    if at(Tok.Query) then
      advance()
      Trees.Query(parseExpr(Parser.LvlSemi))(spanFrom(start))
    else
      val name =
        if at(Tok.RuleName) then
          val rn = advance()
          Some(Trees.Ident(rn.text.drop(1))(rn.span))
        else None
      val e = parseExpr(Parser.LvlSemi)
      if at(Tok.Turnstile) then
        advance()
        resync()
        val body = parseExpr(Parser.LvlSemi)
        Trees.Rule(name, conjuncts(e), Some(body))(spanFrom(start))
      else Trees.Rule(name, List(e), None)(spanFrom(start))

  /** After `$` (at `start`): a hole, a sequence hole or a higher-order hole. */
  protected def parseDollar(start: Int): Tree =
    val seq = at(Tok.DotDot)
    if seq then advance()
    // the expression of a hole does not start in column 0 (it would be the next item)
    if !startsExpression(kind) || atColumn0(position) then
      val at = if atColumn0(position) then insertionPoint else tok.span
      error(SyntaxError.Expected(List(Expect.expression), found, at, None, Some(SyntaxHelp.DollarWithoutExpression)))
      ErrorTree(Nil)(spanFrom(start))
    else if seq then
      val arg = parsePostfix()
      SpliceSeq(arg)(spanFrom(start))
    else
      val arg = parsePostfix()
      if at(Tok.LBrack) && !tok.spaceBefore then
        val open = advance()
        val args = mutable.ListBuffer(parseExpr(Parser.LvlComma + 1))
        while at(Tok.Comma) do
          advance()
          resync()
          args += parseExpr(Parser.LvlComma + 1)
        val closed = close(open, Tok.RBrack)
        checked(SpliceHO(arg, args.toList)(spanFrom(start)), closed)
      else SpliceE(arg)(spanFrom(start))

  /** At `[`: whether it starts a list rather than a lambda `[x] e` / `[x : A] e`. */
  protected def listAhead: Boolean =
    var k = 1
    var depth = 0
    var comma = false
    while depth >= 0 && peekTok(k).kind != Tok.EOF do
      peekTok(k).kind match
        case Tok.LBrack | Tok.LParen | Tok.LBrace => depth += 1
        case Tok.RBrack | Tok.RParen | Tok.RBrace => depth -= 1
        case Tok.Comma if depth == 0 => comma = true
        case _ =>
      if depth >= 0 then k += 1
    val close = k
    val lambdaShape = close >= 2 && (peekTok(1).kind == Tok.Var || peekTok(1).kind == Tok.Name) &&
      (close == 2 || peekTok(2).kind == Tok.Colon)
    // a lambda's body does not start in column 0: that token is the next item (`f X = [X]` without its
    // period, followed by `g : …`, is a list)
    comma || !lambdaShape || !startsLambdaBody(peekTok(close + 1).kind) || atColumn0((i + close + 1).min(toks.length - 1))

  private def startsLambdaBody(t: Tok): Boolean = t != Tok.RuleName && t != Tok.Error && startsExpression(t)

  /** `[e₁, …, eₙ]`, at `[`. */
  protected def parseList(): Tree =
    val open = advance()
    if strayOpener(Tok.RBrack) then
      error(SyntaxError.Unclosed(open.text, open.span, "]", insertionPoint, found, tok.span))
      return ErrorTree(Nil)(open.span)
    val elems = mutable.ListBuffer.empty[Tree]
    if !at(Tok.RBrack) then
      var more = true
      while more do
        elems += listElement()
        if at(Tok.Comma) then
          advance()
          resync()
        else more = false
    val closed = close(open, Tok.RBrack)
    checked(ListLit(elems.toList)(spanFrom(open.span.start)), closed)

  /** A list element; a `:-` after it is the rule syntax of old, which is written in a quote now. */
  private def listElement(): Tree =
    val e = parseExpr(Parser.LvlComma + 1)
    if at(Tok.Turnstile) then ruleOutsideQuote()
    e

  /** At `:-` in parentheses or a list: reported with the quote syntax as help (the enclosing construct
   *  skips to its closing delimiter). */
  protected def ruleOutsideQuote(): Unit =
    error(SyntaxError.Expected(List(Expect.expression), found, tok.span, None, Some(SyntaxHelp.RuleOutsideQuote(tok.span))))

  private def conjuncts(t: Tree): List[Tree] = t match
    case Conj(a, b) => conjuncts(a) ++ conjuncts(b)
    case other => List(other)
