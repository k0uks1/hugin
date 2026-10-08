package hugin.syntax

import scala.collection.mutable

/** The grammar of directives (reference: directives), mixed into [[Parser]]. A directive is the application
 *  of a meta function, `%d a₁ … aₙ.`; its arguments are atoms (names, paths, variables, literals, rule
 *  names `@r`, parenthesised expressions) and mode items `+e -t` (one argument for a run of them,
 *  [[ModeArgs]], elaborated to the prelude's `modes` data: `%demand typed +e +g -t.`). In the prefix form
 *  `%d a₁ … aₙ DECL` it is attached to the declaration that follows, which is recognised by its `:` (the
 *  declaration's head is the name before the `:` with its parameters). What a directive means is decided
 *  by elaboration: the parser knows only the forms with a grammar of their own:
 *
 *  - `%infix assoc p name` (operators are resolved while parsing);
 *  - `%partial` (removed) and `%complete` (only in signatures, [[RecordSyntax]]).
 */
private[syntax] trait DirectiveSyntax extends ParserBase:
  /** Items parsed along with the current one (the declaration after a prefix directive). */
  protected val followingItems: mutable.ListBuffer[Trees.Item] = mutable.ListBuffer.empty

  protected def parseDirective(): Trees.Item =
    val start = tok.span.start
    val d = advance()
    val name = d.text.drop(1)
    def directive(args: DirArgs) = Directive(name, args)(spanFrom(start), d.span)
    name match
      case "infix" =>
        val a = expectTok(Tok.Name, "`left`, `right` or `none`")
        if !Set("left", "right", "none")(a.text) then report(SyntaxError.UnknownAssociativity(a.text, a.span))
        val p = expectTok(Tok.IntLit, "a precedence")
        val n = expectTok(Tok.Name, "an operator name")
        expectPeriod("`.` after directive")
        directive(DirArgs.Infix(a.text, p.value match { case l: Long => l.toInt; case _ => 0 }, Ident(n.text)(n.span)))
      case "partial" => fail(SyntaxError.RemovedPartial(d.span))
      case "complete" => fail(SyntaxError.CompleteOutsideSignature(d.span))
      case _ =>
        val declAt = attachedDeclaration()
        val args = mutable.ListBuffer.empty[Tree]
        while kind != Tok.Period && kind != Tok.EOF && kind != Tok.RBrace && !declAt.contains(position) do
          args += (if kind == Tok.Plus || kind == Tok.Minus then parseModeArgs() else parsePostfix())
        declAt match
          case Some(_) =>
            val decl = Ident(tok.text)(tok.span)
            val dir = directive(DirArgs.Apply(args.toList, Some(decl)))
            followingItems += parseItem()
            dir
          case None =>
            expectPeriod("`.` after directive")
            directive(DirArgs.Apply(args.toList, None))

  /** Mode items `+e -t +`: `+` an input, `-` an output, each optionally naming the column's label. */
  private def parseModeArgs(): Tree =
    val start = tok.span.start
    val b = mutable.ListBuffer.empty[ModeItem]
    while kind == Tok.Plus || kind == Tok.Minus do
      val t = advance()
      val lbl = if kind == Tok.Name then
        val n = advance(); Some(Ident(n.text)(n.span))
      else None
      b += ModeItem(t.kind == Tok.Plus, lbl, t.span.to(lbl.map(_.span).getOrElse(t.span)))
    ModeArgs(b.toList)(spanFrom(start))

  /** The index of the token that starts the declaration a prefix directive is attached to: the name in
   *  front of the first `:` (and of the declaration's parameters) at depth 0 before the end of the item. */
  private def attachedDeclaration(): Option[Int] =
    var k = position
    var depth = 0
    var colon = -1
    var done = false
    while !done do
      tokenAt(k).kind match
        case Tok.LParen | Tok.LBrack | Tok.LBrace => depth += 1
        case Tok.RParen | Tok.RBrack => depth -= 1
        case Tok.RBrace => if depth == 0 then done = true else depth -= 1
        case Tok.Colon if depth == 0 => colon = k; done = true
        case Tok.Period if depth == 0 => done = true
        case Tok.EOF => done = true
        case _ =>
      k += 1
    if colon < 0 then None
    else
      // skip the parameters `X` and `(x : T)` backwards to the declaration's name
      var j = colon - 1
      var ok = true
      while ok && j >= position && tokenAt(j).kind != Tok.Name do
        tokenAt(j).kind match
          case Tok.Var => j -= 1
          case Tok.RParen =>
            var d = 1
            j -= 1
            while j >= position && d > 0 do
              tokenAt(j).kind match
                case Tok.RParen => d += 1
                case Tok.LParen => d -= 1
                case _ =>
              j -= 1
          case _ => ok = false
      Option.when(ok && j >= position && tokenAt(j).kind == Tok.Name)(j)
