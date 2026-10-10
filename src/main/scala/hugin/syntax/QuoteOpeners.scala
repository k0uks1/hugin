package hugin.syntax

import hugin.util.Span

import scala.collection.mutable

/** Recovery of damaged quote openers, before parsing (`docs/PARSER.md`, §4.3). The lexer reports a prime
 *  `'` that no `(` follows right away, and gives it as a [[Tok.Quote]] token alone. This pass decides what
 *  it was meant to be, from the tokens after it:
 *
 *  - `' (`, with a space: the quote's opener (the `(` follows);
 *  - `' {(`, a token between the prime and the parenthesis on its line: the token is dropped (a token of
 *    the lexer's errors is moved into the quote);
 *  - `' p X )`, the parenthesis lost: a `)` closes the quote ahead, at depth 0 before the end of the
 *    item, so an empty `(` is inserted;
 *  - otherwise (also before a closer, `$..B ' )`) the prime is dropped, as a character the lexer did not
 *    recognise.
 *
 *  The parser reads such a quote without further errors in it until it resynchronises: the lexer reported
 *  the mistake. */
object QuoteOpeners:
  def repair(toks: Vector[Token]): Vector[Token] =
    if !toks.exists(_.kind == Tok.Quote) then toks
    else
      val out = mutable.ArrayBuffer.empty[Token]
      var j = 0
      while j < toks.length do
        val t = toks(j)
        // the token list ends with the end of the file: a prime has one token after it
        if t.kind != Tok.Quote || toks(j + 1).kind == Tok.LParen then out += t
        else if j + 2 < toks.length && toks(j + 2).kind == Tok.LParen && toks(j + 2).span.startLine == t.span.startLine then
          out += t
          // the token in between is dropped; one of the lexer's errors is kept, in the quote, so that the
          // parser sees it and damages the entry
          if toks(j + 1).kind == Tok.Error then
            out += toks(j + 2) += toks(j + 1)
            j += 2
          else j += 1
        // a closer right after the prime (`$..B ' )`) closes something else: the prime is stray
        else if !Set(Tok.RParen, Tok.RBrack, Tok.RBrace)(toks(j + 1).kind) && closedAhead(toks, j + 1) then
          val at = toks(j + 1).span.start
          out += t += Token(Tok.LParen, "", Span(t.span.source, at, at), spaceBefore = true)
        j += 1
      out.toVector

  /** Whether a `)` at depth 0 follows the index `k`, before a period at depth 0 that ends the item (one
   *  that no `)` follows on its line), a token in column 0 of a later line, another closing delimiter or
   *  the end of the file. */
  private def closedAhead(toks: Vector[Token], k: Int): Boolean =
    def column0(j: Int) = toks(j).span.startCol == 0 && toks(j - 1).span.startLine < toks(j).span.startLine
    def parenOnLine(j: Int): Boolean =
      toks.iterator.drop(j).takeWhile(t => t.kind != Tok.EOF && t.span.startLine == toks(j - 1).span.startLine).exists(_.kind == Tok.RParen)
    var j = k
    var depth = 0
    while j < toks.length do
      toks(j).kind match
        case Tok.EOF => return false
        case _ if j > k && column0(j) => return false
        case Tok.LParen | Tok.LBrack | Tok.LBrace => depth += 1
        case Tok.RParen if depth == 0 => return true
        case Tok.RParen | Tok.RBrack | Tok.RBrace => if depth == 0 then return false else depth -= 1
        case Tok.Period if depth == 0 && !parenOnLine(j + 1) => return false
        case _ =>
      j += 1
    false
