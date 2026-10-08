package hugin.syntax

import scala.collection.mutable

/** The grammar of reflection (reference: reflection), mixed into [[Parser]]:
 *
 *  - holes `$x`, sequence holes `$..xs` and higher-order holes `$f[t̄]` (the `[` directly after `f`);
 *  - meta lists `[]`, `[e₁, …, eₙ]` and `e :: es`. A `[` starts a list unless it has the shape of a
 *    lambda `[x] e` (one name, optionally typed, followed by an expression); a list element may be a rule
 *    `h :- b`, whose body extends to the closing `]` (so `[h :- a, b]` is one rule; several rules with
 *    bodies are parenthesised);
 *  - rules as expressions and patterns, `(h̄ :- b)` (`(h :-)` without a body).
 */
private[syntax] trait QuoteSyntax extends ParserBase:
  /** After `$` (at `start`): a hole, a sequence hole or a higher-order hole. */
  protected def parseDollar(start: Int): Tree =
    val seq = at(Tok.DotDot)
    if seq then advance()
    // the expression of a hole does not start in column 0 (it would be the next item)
    if !startsExpression(kind) || atColumn0(position) then
      error(SyntaxError.Expected(List(Expect.expression), found, tok.span, None, Some(SyntaxHelp.DollarWithoutExpression)))
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
    comma || !lambdaShape || !startsLambdaBody(peekTok(close + 1).kind)

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

  private def listElement(): Tree =
    val start = tok.span.start
    val e = parseExpr(Parser.LvlComma + 1)
    if at(Tok.Turnstile) then
      advance()
      val body = parseExpr(Parser.LvlSemi)
      RuleQuote(List(e), Some(body))(spanFrom(start))
    else e

  /** The rest of `(h̄ :- b)` at `:-`, after the heads `inner` (a conjunction for several heads); `open` is
   *  the opening parenthesis, closed here. */
  protected def ruleQuoteRest(open: Token, inner: Tree): Tree =
    advance()
    val body = if at(Tok.RParen) then None else Some(parseExpr(Parser.LvlSemi))
    val closed = close(open, Tok.RParen)
    checked(RuleQuote(conjuncts(inner), body)(spanFrom(open.span.start)), closed)

  private def conjuncts(t: Tree): List[Tree] = t match
    case Conj(a, b) => conjuncts(a) ++ conjuncts(b)
    case other => List(other)
