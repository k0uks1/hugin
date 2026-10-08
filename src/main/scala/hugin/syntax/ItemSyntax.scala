package hugin.syntax

import scala.collection.mutable

/** Programs and items (reference: lexical-structure, items), mixed into [[Parser]]: declarations,
 *  definitions, clauses with `where` blocks, subtyping edges, rules and queries; directives are in
 *  [[DirectiveSyntax]]. */
private[syntax] trait ItemSyntax extends ParserBase:
  self: DirectiveSyntax =>
  import Parser.*

  def parseProgram(): Program =
    val items = mutable.ListBuffer.empty[Item]
    while kind != Tok.EOF do
      if kind == Tok.RBrace then
        reporter.report(SyntaxError.UnmatchedBrace(tok.span))
        advance()
      else parseItemRecovering().foreach(items += _)
    Program(items.toList, hugin.util.Span(src, 0, src.content.length))

  /** An item (and the declaration a prefix directive is attached to), or none after an error. */
  protected def parseItemRecovering(): List[Item] =
    val start = i
    followingItems.clear()
    try parseItem() :: followingItems.toList
    catch
      case _: ParseError =>
        sync(start)
        Nil

  /** Skip to the end of the current item: a period at nesting depth 0, or a `}` closing the enclosing body. */
  private def sync(start: Int): Unit =
    var depth = 0
    // count nesting opened since the item start but before the error point
    var k = start
    while k < i do
      toks(k).kind match
        case Tok.LBrace | Tok.LParen | Tok.LBrack => depth += 1
        case Tok.RBrace | Tok.RParen | Tok.RBrack => depth = (depth - 1).max(0)
        case _ =>
      k += 1
    var done = false
    if i == start && kind != Tok.EOF then advance()
    while !done && kind != Tok.EOF do
      if depth == 0 && atLineStart(tok) && kind != Tok.Period then return
      kind match
        case Tok.LBrace | Tok.LParen | Tok.LBrack => depth += 1; advance()
        case Tok.RParen | Tok.RBrack => depth = (depth - 1).max(0); advance()
        case Tok.RBrace =>
          if depth == 0 then done = true else { depth -= 1; advance() }
        case Tok.Period if depth == 0 => advance(); done = true
        case _ => advance()

  protected def parseItem(): Item =
    val start = tok.span.start
    val startCol = tok.span.startCol
    kind match
      case Tok.Directive => parseDirective()
      case Tok.Query =>
        advance()
        val body = parseExpr(LvlSemi)
        expectTok(Tok.Period)
        Query(body)(spanFrom(start))
      case Tok.RuleName =>
        val rn = advance()
        val name = Ident(rn.text.drop(1))(rn.span)
        parseRuleRest(Some(name), start, parseExpr(LvlHead))
      case _ =>
        val lhs = parseExpr(LvlHead)
        kind match
          case Tok.Colon => parseDeclRest(lhs, start)
          case Tok.Eq =>
            advance()
            val rhs = parseExpr(LvlSemi)
            val where = if kind == Tok.KwWhere then parseWhere(startCol) else Nil
            if where.isEmpty then expectTok(Tok.Period, "`.` after clause")
            if where.isEmpty && isDeclHead(lhs) then
              val (name, params) = declHead(lhs)
              Def(name, params, rhs)(spanFrom(start))
            else Clause(lhs, rhs, where)(spanFrom(start))
          case Tok.SubT =>
            advance()
            val sup = parseExpr(LvlBar)
            expectTok(Tok.Period, "`.` after subtyping edge")
            SubEdge(lhs, sup)(spanFrom(start))
          case _ => parseRuleRest(None, start, lhs)

  /** The rest of a declaration `lhs : type [<: sup] [= defn].`, at the `:`. */
  protected def parseDeclRest(lhs: Tree, start: Int): Item =
    expectTok(Tok.Colon)
    val (name, params) = declHead(lhs)
    val tpe = parseType()
    val sup = if kind == Tok.SubT then { advance(); Some(parseType(LvlBar)) }
    else None
    val defn = if kind == Tok.Eq then { advance(); Some(parseNonType(LvlSemi)) }
    else None
    expectTok(Tok.Period, "`.` after declaration")
    Decl(name, params, tpe, sup, defn)(spanFrom(start))

  private def parseRuleRest(name: Option[Ident], start: Int, first: Tree): Item =
    val heads = mutable.ListBuffer(first)
    while kind == Tok.Comma do
      advance()
      heads += parseExpr(LvlHead)
    val body =
      if kind == Tok.Turnstile then { advance(); Some(parseExpr(LvlSemi)) }
      else None
    if kind != Tok.Period then
      if kind == Tok.Colon && name.isDefined then
        fail(SyntaxError.RuleNameOnDeclaration(tok.span))
      expectTok(Tok.Period, if body.isEmpty then "`.`, `,` or `:-`" else "`.` after rule body")
    else advance()
    Rule(name, heads.toList, body)(spanFrom(start))

  /** `where b₁. … bₙ.` after the right-hand side of a clause starting at column `col`. Layout: the block
   *  consists of the items that follow and start at a column greater than `col`; it ends before the first
   *  item at column `col` or less (so a top-level clause's block ends at the next item at column 0), at a
   *  `}`, or at the end of the file. The last binding's period ends the clause. */
  private def parseWhere(col: Int): List[Item] =
    val w = advance()
    val items = mutable.ListBuffer.empty[Item]
    while kind != Tok.EOF && kind != Tok.RBrace && (items.isEmpty || tok.span.startCol > col) do
      parseItemRecovering().foreach(items += _)
    if items.isEmpty then
      reporter.report(SyntaxError.EmptyWhere(w.span))
    items.toList

  /** Whether `lhs` has the shape of a definition head `name param*` (see [[declHead]]). */
  private def isDeclHead(lhs: Tree): Boolean =
    val (hd, args) = TreeOps.flattenApp(lhs)
    hd.isInstanceOf[Ident] && args.forall {
      case _: VarRef => true
      case Ascribe(_: Ident | _: VarRef, _) => true
      case _ => false
    }

  private def declHead(lhs: Tree): (Ident, List[Param]) =
    def flatten(t: Tree, acc: List[Tree]): (Tree, List[Tree]) = t match
      case Apply(f, a) => flatten(f, a :: acc)
      case other => (other, acc)
    val (hd, args) = flatten(lhs, Nil)
    val name = hd match
      case id: Ident => id
      case other =>
        reporter.report(SyntaxError.MalformedDeclarationHead(other.span))
        throw new ParseError
    val params = args.map {
      case v: VarRef => Param.VarParam(v)
      case a @ Ascribe(n @ (_: Ident | _: VarRef), t) => Param.Typed(n, t, a.span)
      case other =>
        reporter.report(SyntaxError.MalformedParameter(other.span))
        throw new ParseError
    }
    (name, params)
