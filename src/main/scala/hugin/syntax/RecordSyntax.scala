package hugin.syntax

import scala.collection.mutable

/** Braces (Section 2.2), mixed into [[Parser]]: record types (signatures, with the requirement
 *  `%complete l`), record values and named patterns `{ l = e, .. }`, implicit binders `{A B : T}` and
 *  module bodies `{ items }`. */
private[syntax] trait RecordSyntax extends ParserBase:
  /** `{ … }`, at `{`: disambiguated by its first tokens. */
  protected def parseBraces(): Tree =
    val start = tok.span.start
    advance()
    val k0 = kind
    val k1 = peekTok(1).kind
    if k0 == Tok.DotDot then
      advance(); expectTok(Tok.RBrace)
      RecordLit(Nil, rest = true)(spanFrom(start))
    else if k0 == Tok.Var && implicitBinderAhead then
      val names = mutable.ListBuffer.empty[Tree]
      while kind == Tok.Var || kind == Tok.Name do
        val n = advance()
        names += (if n.kind == Tok.Var then VarRef(n.text)(n.span) else Ident(n.text)(n.span))
      expectTok(Tok.Colon)
      val tpe = parseType()
      expectTok(Tok.RBrace, "`}` after implicit binder")
      ImplicitBinder(names.toList, tpe)(spanFrom(start))
    else if ((k0 == Tok.Name && k1 == Tok.Colon) || (k0 == Tok.Directive && tok.text == "%complete")) && !periodFirst then
      parseRecordType(start)
    else if k0 == Tok.Name && k1 == Tok.Eq && !periodFirst then parseRecordLit(start)
    else
      val items = mutable.ListBuffer.empty[Item]
      while kind != Tok.RBrace && kind != Tok.EOF do
        parseItemRecovering().foreach(items += _)
      if kind == Tok.EOF then
        reporter.report(SyntaxError.UnclosedModuleBody(hugin.util.Span(src, start, start + 1)))
        throw new ParseError
      advance()
      ModuleBody(items.toList)(spanFrom(start))

  /** At `{A B ... :` (after the brace): implicit binders. */
  private def implicitBinderAhead: Boolean =
    var k = i
    while toks(k).kind == Tok.Var || toks(k).kind == Tok.Name do k += 1
    k > i && toks(k).kind == Tok.Colon

  /** Brace disambiguation (refines Section 2.2): a module body is recognised by a period at depth 0
   *  before the first `,` or the closing `}`; otherwise `l :` starts a record type and `l =` a record. */
  private def periodFirst: Boolean =
    var k = i
    var depth = 0
    while k < toks.length do
      toks(k).kind match
        case Tok.LBrace | Tok.LParen | Tok.LBrack => depth += 1
        case Tok.RParen | Tok.RBrack => depth -= 1
        case Tok.RBrace => if depth == 0 then return false else depth -= 1
        case Tok.Comma if depth == 0 => return false
        case Tok.Period if depth == 0 => return true
        case Tok.EOF => return false
        case _ =>
      k += 1
    false

  /** `{ entries }` after the `{` at `start`: a record type. */
  protected def parseRecordType(start: Int): Tree =
    val entries = mutable.ListBuffer.empty[SigEntry]
    var continue = true
    while continue do
      if kind == Tok.Directive && tok.text == "%complete" then
        val d = advance()
        val l = expectTok(Tok.Name, "a label")
        entries += SigEntry.Complete(Ident(l.text)(l.span), d.span.to(l.span))
      else
        val l = expectTok(Tok.Name, "a label")
        expectTok(Tok.Colon, "`:` in record type")
        entries += SigEntry.FieldDecl(Ident(l.text)(l.span), parseType())
      if kind == Tok.Comma then advance() else continue = false
    expectTok(Tok.RBrace, "`,` or `}`")
    RecordType(entries.toList)(spanFrom(start))

  /** `{ l = e, … }` (possibly ending in `..`) after the `{` at `start`. */
  protected def parseRecordLit(start: Int): Tree =
    val fields = mutable.ListBuffer.empty[Field]
    var rest = false
    var continue = true
    while continue do
      if kind == Tok.DotDot then
        advance(); rest = true; continue = false
      else
        val l = expectTok(Tok.Name, "a label")
        expectTok(Tok.Eq, "`=` in record")
        fields += Field(Ident(l.text)(l.span), parseNonType(Parser.LvlArrow))
        if kind == Tok.Comma then advance() else continue = false
    expectTok(Tok.RBrace, if rest then "`}` after `..`" else "`,` or `}`")
    RecordLit(fields.toList, rest)(spanFrom(start))
