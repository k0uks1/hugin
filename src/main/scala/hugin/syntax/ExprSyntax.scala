package hugin.syntax

/** Expressions (reference: lexical-structure, operators and precedence), mixed into [[Parser]]: a
 *  precedence-climbing loop over the binary operators, prefix operators (`not`, unary `-`, lambdas
 *  `[x] e`), application by juxtaposition, selection `e.l` and the primary expressions. Precedence levels
 *  are those of [[Parser]]; an operator declared with `%infix assoc p name` gets level `10*p + 5`. */
private[syntax] trait ExprSyntax extends ParserBase:
  self: QuoteSyntax =>
  import Parser.*

  private def infixAt(t: Token): Option[(String, Int, Assoc)] = t.kind match
    case Tok.Semi => Some((";", LvlSemi, Assoc.Left))
    case Tok.Comma => Some((",", LvlComma, Assoc.Left))
    case Tok.Arrow => Some(("->", LvlArrow, Assoc.Right))
    case Tok.ColonColon => Some(("::", LvlCons, Assoc.Right))
    case Tok.Bar => Some(("|", LvlBar, Assoc.Left))
    case Tok.Eq => Some(("=", LvlCmp, Assoc.NonAssoc))
    case Tok.Neq => Some(("<>", LvlCmp, Assoc.NonAssoc))
    case Tok.Lt => Some(("<", LvlCmp, Assoc.NonAssoc))
    case Tok.Le => Some(("<=", LvlCmp, Assoc.NonAssoc))
    case Tok.Gt => Some((">", LvlCmp, Assoc.NonAssoc))
    case Tok.Ge => Some((">=", LvlCmp, Assoc.NonAssoc))
    case Tok.Plus => Some(("+", LvlAdd, Assoc.Left))
    case Tok.Minus => Some(("-", LvlAdd, Assoc.Left))
    case Tok.Caret => Some(("^", LvlAdd, Assoc.Left))
    case Tok.Star => Some(("*", LvlMul, Assoc.Left))
    case Tok.Slash => Some(("/", LvlMul, Assoc.Left))
    case Tok.Name => infixOps.get(t.text).map((a, l) => (t.text, l, a))
    case _ => None

  def parseExpr(minLevel: Int): Tree =
    var lhs = parsePrefix(minLevel)
    var continue = true
    var lastNonAssoc = -1
    var chained = false
    while continue do
      infixAt(tok) match
        case Some((op, lvl, assoc)) if lvl >= minLevel && !(inType && lvl == LvlCmp) =>
          if assoc == Assoc.NonAssoc && lastNonAssoc == lvl then
            error(SyntaxError.NonAssociativeChain(op, tok.span))
            chained = true
          val opTok = advance()
          // a separator of a rule body: the conjuncts and disjuncts are recovery regions
          if opTok.kind == Tok.Comma || opTok.kind == Tok.Semi then resync()
          val rhsMin = assoc match
            case Assoc.Right => lvl
            case _ => lvl + 1
          val rhs = parseExpr(rhsMin)
          val sp = lhs.span.to(rhs.span)
          lhs = op match
            case ";" => Disj(lhs, rhs)(sp)
            case "," => Conj(lhs, rhs)(sp)
            case "|" => Union(lhs, rhs)(sp)
            case "::" => ConsE(lhs, rhs)(sp)
            case "->" =>
              lhs match
                case ImplicitBinder(ns, t) => ImplicitPi(ns, t, rhs)(sp)
                case RecordType(List(SigEntry.FieldDecl(l, t))) => ImplicitPi(List(l), t, rhs)(sp)
                case Ascribe(l: Ident, t) => Arrow(Some(l), t, rhs)(sp)
                case _ => Arrow(None, lhs, rhs)(sp)
            case _ if opTok.kind == Tok.Name =>
              // `%infix` operators are resolved into applications (Section 2.2)
              Apply(Apply(Ident(op)(opTok.span), lhs)(lhs.span.to(opTok.span)), rhs)(sp)
            case _ => Infix(op, lhs, rhs)(sp, opTok.span)
          lastNonAssoc = if assoc == Assoc.NonAssoc then lvl else -1
        case _ => continue = false
    checked(lhs, !chained)

  private def parsePrefix(minLevel: Int): Tree =
    val start = tok.span.start
    kind match
      case Tok.KwNot =>
        advance()
        val arg = parseApp()
        Not(arg)(spanFrom(start))
      case Tok.Minus =>
        advance()
        val arg = parseApp()
        arg match
          case Lit(Literal.IntL(v)) => Lit(Literal.IntL(-v))(spanFrom(start))
          case Lit(Literal.FloatL(v)) => Lit(Literal.FloatL(-v))(spanFrom(start))
          case other => Neg(other)(spanFrom(start))
      case Tok.LBrack if !listAhead =>
        // a lambda `[x] e` / `[x : A] e` (the shape is checked by `listAhead`)
        val open = advance()
        val p = advance()
        val param: Tree = if p.kind == Tok.Var then VarRef(p.text)(p.span) else Ident(p.text)(p.span)
        val tpe = if at(Tok.Colon) then { advance(); Some(parseType()) }
        else None
        val ok = close(open, Tok.RBrack)
        val body = parseExpr(minLevel.max(LvlSemi))
        checked(Lambda(param, tpe, body)(spanFrom(start)), ok)
      case _ => parseApp()

  private def startsArg(t: Token): Boolean = !atColumn0(i) && (t.kind match
    case Tok.Var | Tok.IntLit | Tok.FloatLit | Tok.StrLit | Tok.LParen | Tok.LBrace => true
    case Tok.Dollar | Tok.Up | Tok.Quote => true
    case Tok.LBrack => listAhead
    case Tok.Name => !infixOps.contains(t.text)
    case _ => false
  )

  private def parseApp(): Tree =
    var f = parsePostfix()
    while startsArg(tok) do
      val a = parsePostfix()
      f = Apply(f, a)(f.span.to(a.span))
    f

  protected def parsePostfix(): Tree =
    var t = parsePrimary()
    while at(Tok.Select) do
      advance()
      // the lexer makes `.` a selector only before a lowercase letter: a name or a keyword
      t =
        if at(Tok.Name) then
          val n = advance()
          Select(t, n.text)(t.span.to(n.span), n.span)
        else
          expected(List(Expect.label))
          damaged(t)
    t

  private def parsePrimary(): Tree =
    val t = tok
    val start = t.span.start
    kind match
      case Tok.Var =>
        advance()
        if t.text == "_" then Wildcard()(t.span) else VarRef(t.text)(t.span)
      case Tok.Name => advance(); Ident(t.text)(t.span)
      case Tok.RuleName => advance(); RuleRef(t.text.drop(1))(t.span)
      case Tok.IntLit =>
        advance()
        t.value match
          case l: Long => Lit(Literal.IntL(l))(t.span)
          case b: BigInt =>
            // only reachable as the operand of unary minus for Long.MinValue
            if b == BigInt(Long.MaxValue) + 1 && i >= 2 && toks(i - 2).kind == Tok.Minus then
              Lit(Literal.IntL(Long.MinValue))(t.span) // negated again by unary minus: -MinValue == MinValue
            else
              report(SyntaxError.IntegerOutOfRange(t.span))
              Lit(Literal.IntL(0))(t.span)
          case _ => Lit(Literal.IntL(0))(t.span)
      case Tok.FloatLit => advance(); Lit(Literal.FloatL(t.value.asInstanceOf[Double]))(t.span)
      case Tok.StrLit => advance(); Lit(Literal.StrL(t.value.asInstanceOf[String]))(t.span)
      case Tok.KwType => advance(); Keyword(Kw.Type)(t.span)
      case Tok.KwRel => advance(); Keyword(Kw.Rel)(t.span)
      case Tok.KwProp => advance(); Keyword(Kw.Prop)(t.span)
      case Tok.KwMin | Tok.KwMax if peekTok(1).kind != Tok.LBrace =>
        // a bound column type `min τ` / `max τ` (an aggregate is followed by `{`)
        advance()
        val tpe = parseApp()
        BoundType(if t.kind == Tok.KwMin then Bound.Min else Bound.Max, tpe)(spanFrom(start))
      case Tok.KwCount | Tok.KwSum | Tok.KwMin | Tok.KwMax => parseAggregate()
      case Tok.LParen => parseParens()
      case Tok.LBrace => parseBraces()
      case Tok.Directive if t.text == "%builtin" =>
        advance()
        expect(Tok.Name) match
          case Some(n) => Builtin(Ident(n.text)(n.span))(spanFrom(start))
          case None => ErrorTree(Nil)(spanFrom(start))
      case Tok.Directive if t.text == "%import" =>
        advance()
        expect(Tok.StrLit) match
          case Some(p) => Import(p.value.asInstanceOf[String])(spanFrom(start), p.span)
          case None => ErrorTree(Nil)(spanFrom(start))
      case Tok.LBrack if listAhead => parseList()
      case Tok.KwNot | Tok.Minus | Tok.LBrack => parsePrefix(LvlSemi)
      case Tok.Dollar =>
        advance()
        parseDollar(start)
      case Tok.Quote => parseQuote()
      case Tok.Up =>
        advance()
        // the operand does not start in column 0 (it would be the next item)
        val arg = if atColumn0(position) then missing(Expect.tpe) else parsePostfix()
        LiftE(arg)(spanFrom(start))
      case _ => missing(if inType then Expect.tpe else Expect.expression)

  /** `count { t | b }`, `sum`, `min`, `max`, at the keyword. */
  private def parseAggregate(): Tree =
    val kw = advance()
    val start = kw.span.start
    val k = kw.kind match
      case Tok.KwCount => AggKind.Count
      case Tok.KwSum => AggKind.Sum
      case Tok.KwMin => AggKind.Min
      case _ => AggKind.Max
    // a stray opening delimiter before the braces (`count ( { X | p X }`): reported once and skipped, and
    // the aggregate is parsed (damaged), so that its `|` and `}` are not errors of their own (issue #83)
    val stray = (at(Tok.LParen) || at(Tok.LBrack)) && peekTok(1).kind == Tok.LBrace
    expect(Tok.LBrace).orElse(Option.when(stray) { advance(); advance() }) match
      case None => ErrorTree(Nil)(spanFrom(start))
      case Some(open) =>
        val term = parseExpr(LvlCmp)
        val bar = expect(Tok.Bar).isDefined
        val body = if bar then parseExpr(LvlSemi) else ErrorTree(Nil)(insertionPoint)
        val closed = close(open, Tok.RBrace)
        checked(Agg(k, term, body)(spanFrom(start)), !stray && bar && closed)

  /** A variable after `as` or before `with`; a lowercase name there is reported (and taken as the variable). */
  private def variable(): Option[VarRef] =
    if at(Tok.Var) then
      val v = advance()
      Some(VarRef(v.text)(v.span))
    else if at(Tok.Name) then
      val n = tok
      error(SyntaxError.Expected(List(Expect.variable), found, n.span, None, Some(SyntaxHelp.LowercaseVariable(n.text, n.span))))
      advance()
      None
    else
      expected(List(Expect.variable))
      None

  private def parseParens(): Tree =
    val open = advance()
    val start = open.span.start
    if strayOpener(Tok.RParen) then
      error(SyntaxError.Unclosed(open.text, open.span, ")", insertionPoint, found, tok.span))
      return ErrorTree(Nil)(open.span)
    if (at(Tok.Var) || at(Tok.Name)) && peekTok(1).kind == Tok.KwWith then
      val v = variable()
      advance()
      val (fields, ok) =
        if !at(Tok.LBrace) then
          expected(List(Expect.Token(Tok.LBrace)))
          (Nil, false)
        else
          parseBraces() match
            case RecordLit(fs, false) => (fs, true)
            case RecordLit(fs, true) =>
              report(SyntaxError.RestInUpdate(tok.span))
              (fs, true)
            case ModuleBody(Nil) => (Nil, true)
            case other =>
              error(SyntaxError.ExpectedUpdateFields(other.span))
              (Nil, false)
      val closed = close(open, Tok.RParen)
      val tree = With(v.getOrElse(VarRef("_")(open.span)), fields)(spanFrom(start))
      return checked(tree, v.isDefined && ok && closed)
    val inner = parseNonType(LvlSemi)
    kind match
      case Tok.KwAs =>
        advance()
        val v = variable()
        val closed = close(open, Tok.RParen)
        v match
          case Some(v) => checked(As(inner, v)(spanFrom(start)), closed)
          case None => ErrorTree(List(inner))(spanFrom(start))
      case Tok.Colon =>
        advance()
        val t = parseType()
        val closed = close(open, Tok.RParen)
        checked(Ascribe(inner, t)(spanFrom(start)), closed)
      case Tok.Turnstile =>
        ruleOutsideQuote()
        close(open, Tok.RParen)
        damaged(inner)
      case _ =>
        val closed = close(open, Tok.RParen)
        checked(Parens(inner)(spanFrom(start)), closed)
