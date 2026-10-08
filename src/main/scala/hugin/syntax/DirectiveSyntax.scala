package hugin.syntax

import hugin.util.diagnostics.msg
import scala.collection.mutable

/** The grammar of directives (docs/REDESIGN.md §7), mixed into [[Parser]]. A directive is the application
 *  of a meta function, `%d a₁ … aₙ.`; its arguments are atoms (names, paths, variables, literals, rule
 *  names `@r`, parenthesised expressions). In the prefix form `%d a₁ … aₙ DECL` it is attached to the
 *  declaration that follows, which is recognised by its `:` (the declaration's head is the name before
 *  the `:` with its parameters). What a directive means is decided by elaboration: the parser knows only
 *  the forms with a grammar of their own:
 *
 *  - `%infix assoc p name` (operators are resolved while parsing);
 *  - `%mode r +l -m` (mode items; until `%demand` replaces it, REDESIGN C3);
 *  - `%fact c : τ̄ -> a.` (a modifier of the declaration, until C3 removes the data/fact split);
 *  - `%partial` (removed) and `%complete` (only in signatures, [[RecordSyntax]]).
 */
private[syntax] trait DirectiveSyntax extends RecordSyntax:
  protected def report(e: SyntaxError): Unit
  protected def fail(e: SyntaxError): Nothing
  protected def expectPeriod(what: String): Unit

  /** The index of the current token, and the token at an index. */
  protected def position: Int
  protected def tokenAt(k: Int): Token

  /** The rest of a declaration `lhs : …` at the `:` (with `%fact`). */
  protected def parseDeclRest(lhs: Tree, start: Int, fact: Boolean): Trees.Item

  /** Parses the item at the current token (the declaration a directive is attached to). */
  protected def parseAttached(): Trees.Item

  /** Items parsed along with the current one (the declaration after a prefix directive). */
  protected val followingItems: mutable.ListBuffer[Trees.Item] = mutable.ListBuffer.empty

  protected def parseDirective(): Trees.Item =
    val start = tok.span.start
    val d = advance()
    val name = d.text.drop(1)
    def directive(args: DirArgs) = Directive(name, args)(spanFrom(start), d.span)
    name match
      case "fact" =>
        // `%fact c : τ̄ -> a.`: a modifier of a constructor or struct declaration
        val lhs = parseExpr(Parser.LvlHead)
        if kind != Tok.Colon then
          fail(
            SyntaxError.Expected(
              msg"`:` after the name of a `%fact` declaration",
              if kind == Tok.EOF then Found.EndOfFile else Found.Token(tok.text),
              tok.span,
              msg"expected `:`",
              Some(msg"`%fact` marks a constructor or struct declaration: `%fact c : int -> t.`")
            )
          )
        parseDeclRest(lhs, start, fact = true)
      case "mode" =>
        val p = parsePath()
        val ms = parseModeItems()
        expectPeriod("`.` after directive")
        directive(DirArgs.Mode(p, ms))
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
        while kind != Tok.Period && kind != Tok.EOF && kind != Tok.RBrace && !declAt.contains(position) do args += parsePostfix()
        declAt match
          case Some(_) =>
            val decl = Ident(tok.text)(tok.span)
            val dir = directive(DirArgs.Apply(args.toList, Some(decl)))
            followingItems += parseAttached()
            dir
          case None =>
            expectPeriod("`.` after directive")
            directive(DirArgs.Apply(args.toList, None))

  /** A relation or path `m.r` (the target of `%mode`). */
  protected def parsePath(): Tree =
    val t = expectTok(Tok.Name, "a relation or path")
    var p: Tree = Ident(t.text)(t.span)
    while kind == Tok.Select do
      advance()
      val n = expectTok(Tok.Name, "a label after `.`")
      p = Select(p, n.text)(p.span.to(n.span), n.span)
    p

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
