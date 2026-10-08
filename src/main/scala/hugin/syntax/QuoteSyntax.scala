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
    if kind == Tok.DotDot then
      advance()
      val arg = parsePostfix()
      SpliceSeq(arg)(spanFrom(start))
    else
      val arg = parsePostfix()
      if kind == Tok.LBrack && !tok.spaceBefore then
        advance()
        val args = mutable.ListBuffer(parseExpr(Parser.LvlComma + 1))
        while kind == Tok.Comma do
          advance()
          args += parseExpr(Parser.LvlComma + 1)
        expectTok(Tok.RBrack, "`]` after the arguments of a higher-order hole")
        SpliceHO(arg, args.toList)(spanFrom(start))
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
    comma || !lambdaShape || !startsExpression(peekTok(close + 1))

  private def startsExpression(t: Token): Boolean = t.kind match
    case Tok.Var | Tok.Name | Tok.IntLit | Tok.FloatLit | Tok.StrLit | Tok.LParen | Tok.LBrace | Tok.LBrack | Tok.Dollar |
        Tok.Up | Tok.KwNot | Tok.Minus | Tok.KwCount | Tok.KwSum | Tok.KwMin | Tok.KwMax | Tok.KwType | Tok.KwRel |
        Tok.KwProp | Tok.Directive =>
      true
    case _ => false

  /** `[e₁, …, eₙ]`, at `[`. */
  protected def parseList(): Tree =
    val start = tok.span.start
    advance()
    val elems = mutable.ListBuffer.empty[Tree]
    if kind != Tok.RBrack then
      var more = true
      while more do
        elems += listElement()
        if kind == Tok.Comma then advance() else more = false
    expectTok(Tok.RBrack, "`,` or `]` in a list")
    ListLit(elems.toList)(spanFrom(start))

  private def listElement(): Tree =
    val start = tok.span.start
    val e = parseExpr(Parser.LvlComma + 1)
    if kind == Tok.Turnstile then
      advance()
      val body = parseExpr(Parser.LvlSemi)
      RuleQuote(List(e), Some(body))(spanFrom(start))
    else e

  /** The rest of `(h̄ :- b)` at `:-`, after the heads `inner` (a conjunction for several heads); the
   *  closing parenthesis is consumed. */
  protected def ruleQuoteRest(start: Int, inner: Tree): Tree =
    advance()
    val body = if kind == Tok.RParen then None else Some(parseExpr(Parser.LvlSemi))
    expectTok(Tok.RParen, "`)` after a rule")
    RuleQuote(conjuncts(inner), body)(spanFrom(start))

  private def conjuncts(t: Tree): List[Tree] = t match
    case Conj(a, b) => conjuncts(a) ++ conjuncts(b)
    case other => List(other)
