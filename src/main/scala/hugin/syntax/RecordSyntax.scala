package hugin.syntax

import scala.collection.mutable

/** The grammar of records (Section 2.2): record types (signatures, with the requirements `%complete l`,
 *  `%mode l m̄` and `%fact` fields), record values and named patterns `{ l = e, .. }`, and the mode items
 *  `+l -m` that `%mode` directives share with signatures. Mixed into [[Parser]]; the braces are
 *  disambiguated there. */
private[syntax] trait RecordSyntax extends ParserBase:
  protected def parseModeItems(): List[ModeItem] =
    val b = mutable.ListBuffer.empty[ModeItem]
    while kind == Tok.Plus || kind == Tok.Minus do
      val t = advance()
      // `+e` names the column labelled `e`
      val lbl = if kind == Tok.Name then
        val n = advance(); Some(Ident(n.text)(n.span))
      else None
      b += ModeItem(t.kind == Tok.Plus, lbl, t.span.to(lbl.map(_.span).getOrElse(t.span)))
    b.toList

  /** `{ entries }` after the `{` at `start`: a record type. */
  protected def parseRecordType(start: Int): Tree =
    val entries = mutable.ListBuffer.empty[SigEntry]
    var continue = true
    while continue do
      if kind == Tok.Directive && tok.text == "%complete" then
        val d = advance()
        val l = expectTok(Tok.Name, "a label")
        entries += SigEntry.Complete(Ident(l.text)(l.span), d.span.to(l.span))
      else if kind == Tok.Directive && tok.text == "%mode" then
        val d = advance()
        val l = expectTok(Tok.Name, "a label")
        val ms = parseModeItems()
        entries += SigEntry.ModeReq(Ident(l.text)(l.span), ms, d.span.to(ms.lastOption.map(_.span).getOrElse(l.span)))
      else
        val fact = kind == Tok.Directive && tok.text == "%fact"
        if fact then advance()
        val l = expectTok(Tok.Name, "a label")
        expectTok(Tok.Colon, "`:` in record type")
        entries += SigEntry.FieldDecl(Ident(l.text)(l.span), parseType(), fact)
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
