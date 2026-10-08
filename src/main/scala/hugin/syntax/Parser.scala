package hugin.syntax

import hugin.util.*
import hugin.util.diagnostics.{Msg, msg}
import scala.language.implicitConversions
import scala.collection.mutable

/** Recursive-descent / precedence-climbing parser for Figure 1.
 *
 *  Precedence levels (Section 2.2) are scaled by 10; an operator declared with `%infix assoc p name`
 *  gets level `10*p + 5`, i.e. it binds tighter than builtin level p and looser than level p+1.
 *
 *  The meta level's syntax (docs/REDESIGN.md §6) includes equational clauses `f p̄ = e.`
 *  ([[Trees.Clause]]), implicit Π types `{A : T} -> B`, explicit splices `$t` and lifts `⇑t`; the syntax
 *  of reflection (holes, lists, rules as expressions) is in [[QuoteSyntax]], records and signatures in
 *  [[RecordSyntax]].
 */
final class Parser(
    src: SourceFile,
    reporter: Reporter,
    infix: Option[Map[String, (Parser.Assoc, Int)]] = None
) extends QuoteSyntax
    with RecordSyntax
    with DirectiveSyntax:
  import Parser.*

  private val toks: Vector[Token] = Lexer(src, reporter).tokenize()
  private var i = 0
  private val infixOps = mutable.HashMap.empty[String, (Assoc, Int)]

  /** True while parsing a type: comparison operators (in particular `=`) end the type. */
  private var inType = false

  protected def parseType(minLevel: Int): Tree =
    val saved = inType
    inType = true
    try parseExpr(minLevel)
    finally inType = saved

  protected def parseNonType(minLevel: Int): Tree =
    val saved = inType
    inType = false
    try parseExpr(minLevel)
    finally inType = saved

  protected def tok: Token = toks(i)
  protected def peekTok(k: Int): Token = toks((i + k).min(toks.length - 1))
  protected def kind: Tok = tok.kind
  protected def advance(): Token = { val t = tok; if i < toks.length - 1 then i += 1; t }
  private def prevEnd: Int = if i == 0 then 0 else toks(i - 1).span.end
  protected def spanFrom(start: Int): Span = Span(src, start, prevEnd.max(start))
  protected def expectTok(k: Tok, what: String): Token = expect(k, what)

  final class ParseError extends Exception(null, null, false, false)

  protected def report(e: SyntaxError): Unit = reporter.report(e)
  protected def expectPeriod(what: String): Unit = expect(Tok.Period, what)
  protected def position: Int = i
  protected def tokenAt(k: Int): Token = toks(k.min(toks.length - 1))
  protected def parseAttached(): Item = parseItem()

  protected def fail(p: SyntaxError): Nothing =
    if kind == Tok.Error then throw new ParseError // already reported by the lexer
    reporter.report(p)
    throw new ParseError

  /** Reports that `what` was expected at the current token, and abandons the item. */
  private def failExpected(what: Msg, label: Msg = Msg.empty, help: Option[Msg] = None): Nothing =
    fail(SyntaxError.Expected(what, found, tok.span, label, help))

  private def found: Found =
    if kind == Tok.EOF then Found.EndOfFile else Found.Token(tok.text)

  private def expect(k: Tok, what: String = ""): Token =
    if kind == k then advance()
    else if kind == Tok.Error then throw new ParseError
    else
      val w = Msg.text(if what.nonEmpty then what else Lexer.describe(k))
      if k == Tok.Period && i > 0 && tok.span.startLine > toks(i - 1).span.startLine then
        // the item probably ends on the previous line
        val prev = toks(i - 1).span
        reporter.report(SyntaxError.MissingPeriod(w, found, Span(src, prev.end, prev.end), tok.span))
        // recover by accepting the item as if the period were present
        return Token(Tok.Period, ".", Span(src, prev.end, prev.end), false)
      failExpected(w, msg"expected $w")

  // ---------------------------------------------------------------- infix prescan

  private def prescanInfix(): Unit =
    var k = 0
    while k + 4 < toks.length do
      if toks(k).kind == Tok.Directive && toks(k).text == "%infix" &&
        toks(k + 1).kind == Tok.Name && toks(k + 2).kind == Tok.IntLit && toks(k + 3).kind == Tok.Name
      then
        val assoc = toks(k + 1).text match
          case "left" => Some(Assoc.Left)
          case "right" => Some(Assoc.Right)
          case "none" => Some(Assoc.NonAssoc)
          case _ => None
        val p = toks(k + 2).value match
          case l: Long => l.toInt
          case _ => 0
        assoc.foreach(a => infixOps(toks(k + 3).text) = (a, p * 10 + 5))
      k += 1

  // ---------------------------------------------------------------- program and items

  /** The operators declared with `%infix` in the source (all of them, wherever they are written). */
  def infixOperators: Map[String, (Assoc, Int)] =
    prescanInfix()
    infixOps.toMap

  def parseProgram(): Program =
    // the operators of the whole file, when this is a slice of it
    infix match
      case Some(ops) => infixOps ++= ops
      case None => prescanInfix()
    val items = mutable.ListBuffer.empty[Item]
    while kind != Tok.EOF do
      if kind == Tok.RBrace then
        reporter.report(SyntaxError.UnmatchedBrace(tok.span))
        advance()
      else parseItemRecovering().foreach(items += _)
    Program(items.toList, Span(src, 0, src.content.length))

  /** An item (and the declaration a prefix directive is attached to), or none after an error. */
  private def parseItemRecovering(): List[Item] =
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

  private def parseItem(): Item =
    val start = tok.span.start
    val startCol = tok.span.startCol
    kind match
      case Tok.Directive => parseDirective()
      case Tok.Query =>
        advance()
        val body = parseExpr(LvlSemi)
        expect(Tok.Period)
        Query(body)(spanFrom(start))
      case Tok.RuleName =>
        val rn = advance()
        val name = Ident(rn.text.drop(1))(rn.span)
        parseRuleRest(Some(name), start, parseExpr(LvlHead))
      case _ =>
        val lhs = parseExpr(LvlHead)
        kind match
          case Tok.Colon => parseDeclRest(lhs, start, fact = false)
          case Tok.Eq =>
            advance()
            val rhs = parseExpr(LvlSemi)
            val where = if kind == Tok.KwWhere then parseWhere(startCol) else Nil
            if where.isEmpty then expect(Tok.Period, "`.` after clause")
            if where.isEmpty && isDeclHead(lhs) then
              val (name, params) = declHead(lhs)
              Def(name, params, rhs)(spanFrom(start))
            else Clause(lhs, rhs, where)(spanFrom(start))
          case Tok.SubT =>
            advance()
            val sup = parseExpr(LvlBar)
            expect(Tok.Period, "`.` after subtyping edge")
            SubEdge(lhs, sup)(spanFrom(start))
          case _ => parseRuleRest(None, start, lhs)

  /** The rest of a declaration `lhs : type [<: sup] [= defn].`, at the `:`. */
  protected def parseDeclRest(lhs: Tree, start: Int, fact: Boolean): Item =
    expect(Tok.Colon)
    val (name, params) = declHead(lhs)
    val tpe = parseType()
    val sup = if kind == Tok.SubT then { advance(); Some(parseType(LvlBar)) }
    else None
    val defn = if kind == Tok.Eq then { advance(); Some(parseNonType(LvlSemi)) }
    else None
    expect(Tok.Period, "`.` after declaration")
    Decl(name, params, tpe, sup, defn, fact)(spanFrom(start))

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
      expect(Tok.Period, if body.isEmpty then "`.`, `,` or `:-`" else "`.` after rule body")
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

  // ---------------------------------------------------------------- expressions

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
                case RecordType(List(SigEntry.FieldDecl(l, t, false))) => ImplicitPi(List(l), t, rhs)(sp)
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
        expect(Tok.RBrack)
        val body = parseExpr(minLevel.max(LvlSemi))
        Lambda(param, tpe, body)(spanFrom(start))
      case _ => parseApp()

  private def atLineStart(t: Token): Boolean =
    t.span.startCol == 0 && i > 0 && toks(i - 1).span.startLine < t.span.startLine

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
      val n = expect(Tok.Name, "a label after `.`")
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
        expect(Tok.LBrace, "`{` after aggregate")
        val term = parseExpr(LvlCmp)
        expect(Tok.Bar, "`|` separating the aggregated term from the body")
        val body = parseExpr(LvlSemi)
        expect(Tok.RBrace)
        Agg(k, term, body)(spanFrom(start))
      case Tok.LParen => parseParens()
      case Tok.LBrace => parseBraces()
      case Tok.Directive if t.text == "%builtin" =>
        advance()
        val n = expect(Tok.Name, "the name of a base type")
        Builtin(Ident(n.text)(n.span))(spanFrom(start))
      case Tok.Directive if t.text == "%import" =>
        advance()
        val p = expect(Tok.StrLit, "a file path in quotes")
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
      expect(Tok.RParen)
      return With(VarRef(v.text)(v.span), fields)(spanFrom(start))
    val inner = parseNonType(LvlSemi)
    kind match
      case Tok.KwAs =>
        advance()
        val v = expect(Tok.Var, "a variable after `as`")
        expect(Tok.RParen)
        As(inner, VarRef(v.text)(v.span))(spanFrom(start))
      case Tok.Colon =>
        advance()
        val t = parseType()
        expect(Tok.RParen)
        Ascribe(inner, t)(spanFrom(start))
      case Tok.Turnstile => ruleQuoteRest(start, inner)
      case _ =>
        expect(Tok.RParen, "`)`")
        Parens(inner)(spanFrom(start))

  private def parseBraces(): Tree =
    val start = tok.span.start
    advance()
    val k0 = kind
    val k1 = peekTok(1).kind
    if k0 == Tok.DotDot then
      advance(); expect(Tok.RBrace)
      RecordLit(Nil, rest = true)(spanFrom(start))
    else if k0 == Tok.Var && implicitBinderAhead then
      val names = mutable.ListBuffer.empty[Tree]
      while kind == Tok.Var || kind == Tok.Name do
        val n = advance()
        names += (if n.kind == Tok.Var then VarRef(n.text)(n.span) else Ident(n.text)(n.span))
      expect(Tok.Colon)
      val tpe = parseType()
      expect(Tok.RBrace, "`}` after implicit binder")
      ImplicitBinder(names.toList, tpe)(spanFrom(start))
    else if ((k0 == Tok.Name && k1 == Tok.Colon) || (k0 == Tok
        .Directive && (tok.text == "%complete" || tok.text == "%fact" && k1 == Tok.Name && peekTok(2).kind == Tok.Colon))) && !periodFirst
    then
      parseRecordType(start)
    else if k0 == Tok.Name && k1 == Tok.Eq && !periodFirst then parseRecordLit(start)
    else
      val items = mutable.ListBuffer.empty[Item]
      while kind != Tok.RBrace && kind != Tok.EOF do
        parseItemRecovering().foreach(items += _)
      if kind == Tok.EOF then
        reporter.report(SyntaxError.UnclosedModuleBody(Span(src, start, start + 1)))
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

object Parser:
  enum Assoc:
    case Left, Right, NonAssoc
  val LvlSemi = 10
  val LvlComma = 20
  val LvlArrow = 30
  val LvlBar = 40

  /** `::`, the meta level's list constructor (right associative). */
  val LvlCons = 45
  val LvlCmp = 50

  /** Items' heads: everything binding tighter than comparisons. */
  val LvlHead = 51
  val LvlAdd = 60
  val LvlMul = 70

  def parse(src: SourceFile, reporter: Reporter): Program = Parser(src, reporter).parseProgram()

  /** The `%infix` operators of a file, which every part of it is parsed with. */
  def infixOperators(src: SourceFile): Map[String, (Assoc, Int)] = Parser(src, Reporter()).infixOperators

  /** Parses a slice of a file (its text from the start of a top-level item to its end) with the file's
   *  `%infix` operators: the items, if it parses without diagnostics. */
  def parseSlice(src: SourceFile, infix: Map[String, (Assoc, Int)]): Option[List[Trees.Item]] =
    val reporter = Reporter()
    val program = Parser(src, reporter, Some(infix)).parseProgram()
    Option.when(reporter.diagnostics.isEmpty)(program.items)
