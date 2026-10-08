package hugin.syntax

import scala.collection.mutable

/** The grammar of records (Section 2.2): record types (signatures, with the requirement `%complete l`),
 *  record values and named patterns `{ l = e, .. }`. Mixed into [[Parser]]; the braces are disambiguated
 *  there. */
private[syntax] trait RecordSyntax extends ParserBase:

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
