package hugin.syntax

import hugin.util.diagnostics.msg
import scala.language.implicitConversions

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
    while continue do
      infixAt(tok) match
        case Some((op, lvl, assoc)) if lvl >= minLevel && !(inType && lvl == LvlCmp) =>
          if assoc == Assoc.NonAssoc && lastNonAssoc == lvl then
            fail(SyntaxError.NonAssociativeChain(op, tok.span))
          val opTok = advance()
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
    lhs

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
          case l @ Lit(Literal.IntL(v)) => Lit(Literal.IntL(-v))(spanFrom(start))
          case l @ Lit(Literal.FloatL(v)) => Lit(Literal.FloatL(-v))(spanFrom(start))
          case other => Neg(other)(spanFrom(start))
      case Tok.LBrack if !listAhead =>
        advance()
        val p = tok
        val param: Tree = p.kind match
          case Tok.Var => advance(); VarRef(p.text)(p.span)
          case Tok.Name => advance(); Ident(p.text)(p.span)
          case _ => failExpected(msg"a lambda parameter", msg"expected a name or variable")
        val tpe = if kind == Tok.Colon then { advance(); Some(parseType()) }
        else None
        expectTok(Tok.RBrack)
        val body = parseExpr(minLevel.max(LvlSemi))
        Lambda(param, tpe, body)(spanFrom(start))
      case _ => parseApp()

  private def startsArg(t: Token): Boolean = !atLineStart(t) && (t.kind match
    case Tok.Var | Tok.IntLit | Tok.FloatLit | Tok.StrLit | Tok.LParen | Tok.LBrace => true
    case Tok.Dollar | Tok.Up => true
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
    while kind == Tok.Select do
      advance()
      val n = expectTok(Tok.Name, "a label after `.`")
      t = Select(t, n.text)(t.span.to(n.span), n.span)
    t

  private def parsePrimary(): Tree =
    val t = tok
    val start = t.span.start
    t.kind match
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
              reporter.report(SyntaxError.IntegerOutOfRange(t.span))
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
      case Tok.KwCount | Tok.KwSum | Tok.KwMin | Tok.KwMax =>
        advance()
        val k = t.kind match
          case Tok.KwCount => AggKind.Count
          case Tok.KwSum => AggKind.Sum
          case Tok.KwMin => AggKind.Min
          case _ => AggKind.Max
        expectTok(Tok.LBrace, "`{` after aggregate")
        val term = parseExpr(LvlCmp)
        expectTok(Tok.Bar, "`|` separating the aggregated term from the body")
        val body = parseExpr(LvlSemi)
        expectTok(Tok.RBrace)
        Agg(k, term, body)(spanFrom(start))
      case Tok.LParen => parseParens()
      case Tok.LBrace => parseBraces()
      case Tok.Directive if t.text == "%builtin" =>
        advance()
        val n = expectTok(Tok.Name, "the name of a base type")
        Builtin(Ident(n.text)(n.span))(spanFrom(start))
      case Tok.Directive if t.text == "%import" =>
        advance()
        val p = expectTok(Tok.StrLit, "a file path in quotes")
        Import(p.value.asInstanceOf[String])(spanFrom(start), p.span)
      case Tok.LBrack if listAhead => parseList()
      case Tok.KwNot | Tok.Minus | Tok.LBrack => parsePrefix(LvlSemi)
      case Tok.Dollar =>
        advance()
        parseDollar(start)
      case Tok.Up =>
        advance()
        val arg = parsePostfix()
        LiftE(arg)(spanFrom(start))
      case Tok.Error => throw new ParseError
      case _ =>
        failExpected(msg"an expression", msg"expected an expression")

  private def parseParens(): Tree =
    val start = tok.span.start
    advance()
    if kind == Tok.Var && peekTok(1).kind == Tok.KwWith then
      val v = advance()
      advance()
      if kind != Tok.LBrace then failExpected(msg"`{` after `with`")
      val fields = parseBraces() match
        case RecordLit(fs, false) => fs
        case RecordLit(fs, true) =>
          reporter.report(SyntaxError.RestInUpdate(tok.span))
          fs
        case ModuleBody(Nil) => Nil
        case other =>
          reporter.report(SyntaxError.ExpectedUpdateFields(other.span))
          Nil
      expectTok(Tok.RParen)
      return With(VarRef(v.text)(v.span), fields)(spanFrom(start))
    val inner = parseNonType(LvlSemi)
    kind match
      case Tok.KwAs =>
        advance()
        val v = expectTok(Tok.Var, "a variable after `as`")
        expectTok(Tok.RParen)
        As(inner, VarRef(v.text)(v.span))(spanFrom(start))
      case Tok.Colon =>
        advance()
        val t = parseType()
        expectTok(Tok.RParen)
        Ascribe(inner, t)(spanFrom(start))
      case Tok.Turnstile => ruleQuoteRest(start, inner)
      case _ =>
        expectTok(Tok.RParen, "`)`")
        Parens(inner)(spanFrom(start))
