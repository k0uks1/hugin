package hugin.syntax

import hugin.util.Span
import scala.collection.mutable

/** Programs and items (reference: lexical-structure, items), mixed into [[Parser]]: declarations,
 *  definitions, clauses with `where` blocks, subtyping edges, rules and queries; directives are in
 *  [[DirectiveSyntax]]. Every item is a recovery region and is kept with what parsed
 *  (`docs/PARSER.md`, §4). */
private[syntax] trait ItemSyntax extends ParserBase:
  self: DirectiveSyntax =>
  import Parser.*

  def parseProgram(): Program =
    val (items, _) = parseItems(!at(Tok.EOF), unexpectedAtTop)
    Program(items, Span(src, 0, src.content.length))

  private def unexpectedAtTop(t: Token): SyntaxError =
    if t.kind == Tok.RBrace then SyntaxError.UnmatchedBrace(t.span)
    else SyntaxError.Expected(List(Expect.item), found, t.span, None)

  protected def parseItem(): List[Item] =
    val first = tok
    val start = first.span.start
    kind match
      case Tok.Directive => parseDirective()
      case Tok.Query =>
        advance()
        // the formula does not start in column 0 (it would be the next item)
        val body = if atColumn0(i) then missing(Expect.expression, Some(Context("query", first.span))) else parseExpr(LvlSemi)
        val ok = endItem(Context("query", first.span), List(Expect.period))
        List(Query(checked(body, ok))(spanFrom(start)))
      case Tok.RuleName =>
        val rn = advance()
        val name = Ident(rn.text.drop(1))(rn.span)
        parseRuleRest(Some(name), first, parseExpr(LvlHead))
      case _ =>
        val lhs = parseExpr(LvlHead)
        kind match
          case Tok.Colon => parseDeclRest(lhs, first)
          case Tok.ColonColon =>
            // `f :: int -> int.`: a type signature as in Haskell
            error(SyntaxError.Expected(List(Expect.Token(Tok.Colon)), found, tok.span, None, Some(SyntaxHelp.DoubleColon(tok.span))))
            parseDeclRest(lhs, first)
          case Tok.Eq => List(parseDefRest(lhs, first))
          case Tok.SubT =>
            advance()
            val sup = parseExpr(LvlBar)
            val ok = endItem(Context("subtyping edge", first.span), List(Expect.period))
            List(SubEdge(lhs, checked(sup, ok))(spanFrom(start)))
          case _ => parseRuleRest(None, first, lhs)

  protected def damagedItem(item: Item): Option[Item] = item match
    case d: Decl =>
      Some(
        if d.defn.isDefined then d.copy(defn = d.defn.map(damaged))(d.span)
        else if d.sup.isDefined then d.copy(sup = d.sup.map(damaged))(d.span)
        else d.copy(tpe = damaged(d.tpe))(d.span)
      )
    case d: Def => Some(d.copy(rhs = damaged(d.rhs))(d.span))
    case c: Clause => Some(c.copy(rhs = damaged(c.rhs))(c.span))
    case e: SubEdge => Some(e.copy(sup = damaged(e.sup))(e.span))
    case q: Query => Some(q.copy(body = damaged(q.body))(q.span))
    case r: Rule =>
      Some(
        if r.body.isDefined then r.copy(body = r.body.map(damaged))(r.span)
        else r.copy(heads = r.heads.init :+ damaged(r.heads.last))(r.span)
      )
    case d @ Directive(_, DirArgs.Apply(args, decl)) =>
      Some(Directive(d.kind, DirArgs.Apply(args :+ ErrorTree(Nil)(d.span), decl))(d.span, d.kindSpan))
    // `%use m.` and `%export S.` end with a complete argument: a stray token after the period does not
    // change what they open or export, so they are kept (dropping `%use` would leave its names unresolved)
    case d @ Directive(_, _: DirArgs.Use | _: DirArgs.Export) => Some(d)
    case _: Directive => None

  /** The rest of a declaration `lhs : type [<: sup] [= defn].`, at the `:` (or a `::` reported already).
   *  A head without a name declares nothing: the item is parsed and dropped. One whose name follows a
   *  stray token (`X sel : τ.`) is damaged: it is not elaborated, and its name is erroneous. */
  private def parseDeclRest(lhs: Tree, first: Token, more: List[Tree] = Nil): List[Item] =
    val colon = advance()
    val (head, strayHead) = declHead(lhs) match
      case Some((name, params, stray)) => (Some((name, params)), stray)
      case None => (None, false)
    // the other names of `a, b, c : type.`: names alone, as the first one
    val others = more.map {
      case id: Ident => Some((id, List.empty[Param]))
      case other =>
        error(SyntaxError.MultiDeclarationHead(other.span))
        None
    }
    if more.nonEmpty && head.exists(_._2.nonEmpty) then error(SyntaxError.MultiDeclarationHead(lhs.span))
    val malformedNames = more.nonEmpty && (head.forall(_._2.nonEmpty) || others.contains(None))
    if more.isEmpty && at(Tok.Eq) && colon.kind == Tok.Colon && !tok.spaceBefore then
      // `x := e`: a definition with a `:` too many (repaired; with a space between them, `x : = e` is
      // only an error: a missing type)
      error(SyntaxError.Expected(List(Expect.tpe), found, tok.span, None, Some(SyntaxHelp.ColonEquals(colon.span))))
      return List(parseDefRest(lhs, first))
    val tpe = parseType() match
      // `T ā : data.`: a shared data declaration (`data` is a keyword only here)
      case d @ Ident("data") if at(Tok.Period) => Keyword(Kw.Data)(d.span)
      case other => other
    val sup = if at(Tok.SubT) then { advance(); Some(parseType(LvlBar)) }
    else None
    // a declaration of several names has no definition
    val defn = if at(Tok.Eq) && more.isEmpty then { advance(); Some(parseNonType(LvlSemi)) }
    else None
    val expectations = if defn.isEmpty && more.isEmpty then List(Expect.period, Expect.Token(Tok.Eq)) else List(Expect.period)
    val ok = endItem(Context("declaration", first.span), expectations) && !strayHead && !malformedNames
    // the part an error after the item damages
    val (tpe1, sup1, defn1) =
      if ok then (tpe, sup, defn)
      else if defn.isDefined then (tpe, sup, defn.map(damaged))
      else if sup.isDefined then (tpe, sup.map(damaged), defn)
      else (damaged(tpe), sup, defn)
    (head.toList ++ others.flatten).map((name, params) => Decl(name, params, tpe1, sup1, defn1)(spanFrom(first.span.start)))

  /** The rest of a definition `f params = e.` or a clause `f p̄ = e [where …].`, at the `=`. */
  private def parseDefRest(lhs: Tree, first: Token): Item =
    val start = first.span.start
    advance()
    val rhs =
      if at(Tok.KwWhere) && startsExpression(peekTok(1).kind) && peekTok(1).span.startLine == tok.span.startLine then
        // `f p = where e`: a stray `where` before the right-hand side, skipped with an error
        expected(List(Expect.expression))
        advance()
        damaged(parseExpr(LvlSemi))
      else parseExpr(LvlSemi)
    val (where, clean) = if at(Tok.KwWhere) then parseWhere(first) else (Nil, true)
    if where.nonEmpty then Clause(lhs, checked(rhs, clean), where)(spanFrom(start))
    else
      val head = defHead(lhs)
      // `(f X) = e.`
      if head.isDefined && lhs.isInstanceOf[Parens] then error(SyntaxError.MalformedDeclarationHead(lhs.span))
      val construct = if head.isDefined then "definition" else "clause"
      val ok = endItem(Context(construct, first.span), List(Expect.period, Expect.Token(Tok.KwWhere)))
      head match
        case Some((name, params)) => Def(name, params, checked(rhs, ok))(spanFrom(start))
        case None => Clause(lhs, checked(rhs, ok), Nil)(spanFrom(start))

  private def parseRuleRest(name: Option[Ident], first: Token, firstHead: Tree): List[Item] =
    val start = first.span.start
    val heads = mutable.ListBuffer(firstHead)
    while at(Tok.Comma) do
      advance()
      resync()
      heads += parseExpr(LvlHead)
    if at(Tok.Colon) && name.isDefined && heads.length == 1 && kind != Tok.Turnstile then
      // `@r name : type.`: the rule name is ignored
      error(SyntaxError.RuleNameOnDeclaration(tok.span))
      return parseDeclRest(firstHead, first)
    // `a, b, c : type.`: a declaration of several names, decided at the `:` (reference: object/declarations)
    if at(Tok.Colon) && name.isEmpty && heads.length > 1 then return parseDeclRest(firstHead, first, heads.toList.tail)
    val body =
      if at(Tok.Turnstile) then
        advance()
        resync()
        // the body does not start in column 0 (it would be the next item)
        Some(if atColumn0(i) then missing(Expect.expression, Some(Context("rule", first.span))) else parseExpr(LvlSemi))
      else None
    val expectations =
      if body.isEmpty then List(Expect.period, Expect.Token(Tok.Comma), Expect.Token(Tok.Turnstile)) else List(Expect.period)
    val construct = if body.isEmpty && heads.length == 1 && name.isEmpty then "fact" else "rule"
    val ok = endItem(Context(construct, first.span), expectations)
    val (heads1, body1) =
      if ok then (heads.toList, body)
      else if body.isDefined then (heads.toList, body.map(damaged))
      else (heads.toList.init :+ damaged(heads.last), body)
    List(Rule(name, heads1, body1)(spanFrom(start)))

  /** `where b₁. … bₙ.` after the right-hand side of a clause starting with `first`. Layout: the block
   *  consists of the items that follow and start at a column greater than the clause's; it ends before
   *  the first item at that column or less (so a top-level clause's block ends at the next item at column
   *  0), at a `}`, or at the end of the file. The last binding's period ends the clause; if there is no
   *  binding, the clause ends as usual. */
  private def parseWhere(first: Token): (List[Item], Boolean) =
    val w = advance()
    val col = first.span.startCol
    if !startsItem(kind) then
      error(SyntaxError.EmptyWhere(w.span))
      (Nil, true)
    else
      val firstBinding = position
      parseItems(
        !at(Tok.EOF) && !at(Tok.RBrace) && (position == firstBinding || tok.span.startCol > col),
        t => SyntaxError.Expected(List(Expect.Thing("a local definition")), found, t.span, Some(Context("clause", first.span)))
      )

  /** The name and parameters of a definition head `name param*`, if `lhs` has that shape (otherwise the
   *  item is a clause with patterns). */
  private def defHead(lhs: Tree): Option[(Ident, List[Param])] =
    val (hd, args) = TreeOps.flattenApp(lhs)
    val params = args.map {
      case v: VarRef => Some(Param.VarParam(v))
      case a @ Ascribe(n @ (_: Ident | _: VarRef), t) => Some(Param.Typed(n, t, a.span))
      case _ => None
    }
    hd match
      case id: Ident if params.forall(_.isDefined) => Some((id, params.flatten))
      case _ => None

  /** The name and parameters of a declaration head, and whether a stray token came before the name. A
   *  malformed parameter is reported and kept ([[Param.Malformed]]); a head in parentheses is reported and
   *  taken without them; a head that starts with another token than a name is reported, and its first
   *  name taken as the declaration's, with the parameters after it (`X sel : τ.`); a head without a name
   *  is reported, and the declaration is dropped. */
  private def declHead(lhs: Tree): Option[(Ident, List[Param], Boolean)] =
    def flatten(t: Tree, acc: List[Tree]): (Tree, List[Tree]) = t match
      case Apply(f, a) => flatten(f, a :: acc)
      case other => (other, acc)
    def unparenthesised(t: Tree): Tree = t match
      case Parens(inner) => unparenthesised(inner)
      case other => other
    val (hd0, args0) = flatten(lhs, Nil)
    var stray = false
    val (name, args) = hd0 match
      case id: Ident => (Some(id), args0)
      case other =>
        error(SyntaxError.MalformedDeclarationHead(other.span))
        unparenthesised(other) match
          case id: Ident => (Some(id), args0)
          case _ =>
            val k = args0.indexWhere(_.isInstanceOf[Ident])
            stray = k >= 0
            if stray then (Some(args0(k).asInstanceOf[Ident]), args0.drop(k + 1)) else (None, args0)
    val params = args.map {
      case v: VarRef => Param.VarParam(v)
      case a @ Ascribe(n @ (_: Ident | _: VarRef), t) => Param.Typed(n, t, a.span)
      case id: Ident =>
        error(SyntaxError.MalformedParameter(id.span, Some(id.name)))
        Param.Malformed(id)
      case other =>
        error(SyntaxError.MalformedParameter(other.span))
        Param.Malformed(other)
    }
    name.map((_, params, stray))
