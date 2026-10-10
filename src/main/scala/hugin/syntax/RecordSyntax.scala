package hugin.syntax

import scala.collection.mutable

/** Braces (Section 2.2), mixed into [[Parser]]: record types (signatures, with the requirement
 *  `%complete l`), record values and named patterns `{ l = e, .. }`, implicit binders `{A B : T}` and
 *  module bodies `{ items }`. */
private[syntax] trait RecordSyntax extends ParserBase:
  /** `{ … }`, at `{`: disambiguated by its first tokens. */
  protected def parseBraces(): Tree =
    val open = advance()
    val start = open.span.start
    val k0 = kind
    val k1 = peekTok(1).kind
    if k0 == Tok.DotDot then
      advance()
      checked(RecordLit(Nil, rest = true)(spanFrom(start)), close(open, Tok.RBrace))
    // a period first makes it a module body (`{ X`⏎`f : t.`, a stray `X`): a binder's type has none
    else if k0 == Tok.Var && implicitBinderAhead && !periodFirst then
      val names = mutable.ListBuffer.empty[Tree]
      while at(Tok.Var) || at(Tok.Name) do
        val n = advance()
        names += (if n.kind == Tok.Var then VarRef(n.text)(n.span) else Ident(n.text)(n.span))
      advance() // the `:` found by `implicitBinderAhead`
      val tpe = parseType()
      checked(ImplicitBinder(names.toList, tpe)(spanFrom(start)), close(open, Tok.RBrace))
    else if ((k0 == Tok.Name && k1 == Tok.Colon) || (k0 == Tok.Directive && tok.text == "%complete")) && !periodFirst then
      parseRecordType(open)
    else if k0 == Tok.Name && k1 == Tok.Eq && !periodFirst then parseRecordLit(open)
    else if k0 == Tok.Comma then
      // no braces start with `,`: the `{` is stray (`{ shop = "n" {, .. }`), and what follows it belongs to
      // the enclosing construct
      expected(List(Expect.label, Expect.item, Expect.Token(Tok.RBrace)))
      ErrorTree(Nil)(open.span)
    else if enclosingClosedFirst then
      // `(arr S { T)`: the enclosing construct closes before any `}`: the `{` is stray and unclosed, and what
      // follows it belongs to the enclosing construct
      error(SyntaxError.Unclosed(open.text, open.span, "}", insertionPoint, found, tok.span))
      ErrorTree(Nil)(open.span)
    else parseModuleBody(open)

  /** The items of a module body up to its `}`. If it is not closed, it ends at the end of the file if
   *  its first item is in column 0 of a line of its own, and otherwise before the first item in column 0
   *  (`docs/PARSER.md`, §4.3). */
  private def parseModuleBody(open: Token): Tree =
    val column0Members = atColumn0(position)
    val (items, clean) =
      inBody(Tok.RBrace, Some(open))(parseItems(
        !at(Tok.RBrace) && !at(Tok.EOF) && (column0Members || !atColumn0(position)),
        unexpectedInBody
      ))
    // `close`: the `}` may be stray (`{ }`⏎`a : t`⏎`}`)
    if at(Tok.RBrace) then checked(ModuleBody(items)(spanFrom(open.span.start)), close(open, Tok.RBrace) && clean)
    else
      resync() // a mistake of its own, also after one in the last item
      error(SyntaxError.Unclosed(open.text, open.span, "}", insertionPoint, found, tok.span))
      damaged(ModuleBody(items)(spanFrom(open.span.start)))

  private def unexpectedInBody(t: Token): SyntaxError =
    SyntaxError.Expected(List(Expect.item, Expect.Token(Tok.RBrace)), found, t.span, None)

  /** After a brace: whether a `)` or `]` at depth 0 comes before a `}` or a period at depth 0. */
  private def enclosingClosedFirst: Boolean =
    var k = i
    var depth = 0
    while k < toks.length do
      toks(k).kind match
        case Tok.LBrace | Tok.LParen | Tok.LBrack => depth += 1
        case Tok.RParen | Tok.RBrack => if depth == 0 then return true else depth -= 1
        case Tok.RBrace => if depth == 0 then return false else depth -= 1
        case Tok.Period if depth == 0 => return false
        case Tok.EOF => return false
        case _ =>
      k += 1
    false

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

  /** A field's label and its separator (`:` in a record type, `=` in a record value; the other one is
   *  reported with a suggestion). None (after an error) if there is no label. */
  private def labelAnd(sep: Tok, inType: Boolean): Option[(Ident, Boolean)] =
    if !at(Tok.Name) then expected(List(Expect.label))
    Option.when(at(Tok.Name))(advance()).map { l =>
      val ok =
        if at(sep) then { advance(); true }
        else if at(if inType then Tok.Eq else Tok.Colon) then
          error(SyntaxError.Expected(List(Expect.Token(sep)), found, tok.span, None, Some(SyntaxHelp.RecordSeparator(tok.span, inType))))
          advance()
          false
        else
          expected(List(Expect.Token(sep)))
          false
      (Ident(l.text)(l.span), ok)
    }

  /** `{ entries }` after the `{` `open`: a record type. An entry without a label ends the entries; the
   *  closing brace recovers. */
  protected def parseRecordType(open: Token): Tree =
    val entries = mutable.ListBuffer.empty[SigEntry]
    var ok = true
    var more = true
    while more do
      if at(Tok.Directive) && tok.text == "%complete" then
        val d = advance()
        if !at(Tok.Name) then expected(List(Expect.label))
        Option.when(at(Tok.Name))(advance()) match
          case Some(l) => entries += SigEntry.Complete(Ident(l.text)(l.span), d.span.to(l.span))
          case None => ok = false
      else
        labelAnd(Tok.Colon, inType = true) match
          case Some((l, sepOk)) =>
            val t = parseType()
            entries += SigEntry.FieldDecl(l, checked(t, sepOk))
          case None => ok = false
      if ok && at(Tok.Comma) then
        advance()
        resync()
      else more = false
    val closed = close(open, Tok.RBrace)
    checked(RecordType(entries.toList)(spanFrom(open.span.start)), ok && closed)

  /** `{ l = e, … }` (possibly ending in `..`) after the `{` `open`. */
  protected def parseRecordLit(open: Token): Tree =
    val fields = mutable.ListBuffer.empty[Field]
    var rest = false
    var ok = true
    var more = true
    while more do
      if at(Tok.DotDot) then
        advance()
        rest = true
        more = false
      else
        labelAnd(Tok.Eq, inType = false) match
          case Some((l, sepOk)) =>
            val v = parseNonType(Parser.LvlArrow)
            fields += Field(l, checked(v, sepOk))
          case None => ok = false
        if ok && at(Tok.Comma) then
          advance()
          resync()
        else more = false
    val closed = close(open, Tok.RBrace)
    checked(RecordLit(fields.toList, rest)(spanFrom(open.span.start)), ok && closed)
