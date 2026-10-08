package hugin.syntax

import hugin.util.*

/** What the parts of the grammar outside [[Parser]] ([[QuoteSyntax]], [[RecordSyntax]]) use of it: the
 *  token stream and the expression parsers. */
private[syntax] trait ParserBase:
  protected def tok: Token
  protected def kind: Tok
  protected def advance(): Token
  protected def peekTok(k: Int): Token
  protected def spanFrom(start: Int): Span

  /** Consumes a token of kind `k`, or reports that `what` was expected and abandons the item. */
  protected def expectTok(k: Tok, what: String): Token
  protected def parsePostfix(): Tree
  def parseExpr(minLevel: Int): Tree

  /** An expression in a type (comparisons end it) or outside one. */
  protected def parseType(minLevel: Int = Parser.LvlArrow): Tree
  protected def parseNonType(minLevel: Int): Tree
