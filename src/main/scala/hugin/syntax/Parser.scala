package hugin.syntax

import hugin.util.*
import scala.collection.mutable

/** Recursive-descent / precedence-climbing parser for Figure 1.
 *
 *  Precedence levels (Section 2.2) are scaled by 10; an operator declared with `%infix assoc p name`
 *  gets level `10*p + 5`, i.e. it binds tighter than builtin level p and looser than level p+1.
 */
final class Parser(src: SourceFile, reporter: Reporter, infix: Option[Map[String, (Parser.Assoc, Int)]] = None):
  import Parser.*

  private val toks: Vector[Token] = Lexer(src, reporter).tokenize()
  private var i = 0
  private val infixOps = mutable.HashMap.empty[String, (Assoc, Int)]

  /** True while parsing a type: comparison operators (in particular `=`) end the type. */
  private var inType = false

  private def parseType(minLevel: Int = LvlArrow): Tree =
    val saved = inType
    inType = true
    try parseExpr(minLevel)
    finally inType = saved

  private def parseNonType(minLevel: Int): Tree =
    val saved = inType
    inType = false
    try parseExpr(minLevel)
    finally inType = saved

  private def tok: Token = toks(i)
  private def peekTok(k: Int): Token = toks((i + k).min(toks.length - 1))
  private def kind: Tok = tok.kind
  private def advance(): Token = { val t = tok; if i < toks.length - 1 then i += 1; t }
  private def prevEnd: Int = if i == 0 then 0 else toks(i - 1).span.end
  private def spanFrom(start: Int): Span = Span(src, start, prevEnd.max(start))

  final class ParseError extends Exception(null, null, false, false)

  private def fail(msg: String, label: String = "", help: Option[String] = None): Nothing =
    if kind == Tok.Error then throw new ParseError // already reported by the lexer
    var d = Diagnostic.error("E0001", msg, tok.span, label)
    help.foreach(h => d = d.withHelp(h))
    reporter.report(d)
    throw new ParseError

  private def found: String =
    if kind == Tok.EOF then "end of file" else s"`${tok.text}`"

  private def expect(k: Tok, what: String = ""): Token =
    if kind == k then advance()
    else if kind == Tok.Error then throw new ParseError
    else
      val w = if what.nonEmpty then what else Lexer.describe(k)
      if k == Tok.Period && i > 0 && tok.span.startLine > toks(i - 1).span.startLine then
        // the item probably ends on the previous line
        val prev = toks(i - 1).span
        reporter.report(
          Diagnostic.error("E0001", s"expected $w, found $found", Span(src, prev.end, prev.end), "expected `.` here")
            .withLabel(tok.span, "next item starts here")
            .withHelp("every item ends with a period")
            .withSuggestion("add `.`", Span(src, prev.end, prev.end), ".")
        )
        // recover by accepting the item as if the period were present
        return Token(Tok.Period, ".", Span(src, prev.end, prev.end), false)
      fail(s"expected $w, found $found", s"expected $w")

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
        reporter.report(Diagnostic.error("E0001", "unmatched `}`", tok.span, "no module body to close"))
        advance()
      else parseItemRecovering().foreach(items += _)
    Program(items.toList, Span(src, 0, src.content.length))

  private def parseItemRecovering(): Option[Item] =
    val start = i
    try Some(parseItem())
    catch
      case _: ParseError =>
        sync(start)
        None

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
            val (name, params) = declHead(lhs)
            val rhs = parseExpr(LvlSemi)
            expect(Tok.Period, "`.` after definition")
            Def(name, params, rhs)(spanFrom(start))
          case Tok.SubT =>
            advance()
            val sup = parseExpr(LvlBar)
            expect(Tok.Period, "`.` after subtyping edge")
            SubEdge(lhs, sup)(spanFrom(start))
          case _ => parseRuleRest(None, start, lhs)

  /** The rest of a declaration `lhs : type [<: sup] [= defn].`, at the `:`. */
  private def parseDeclRest(lhs: Tree, start: Int, fact: Boolean): Item =
    expect(Tok.Colon)
    val (name, params) = declHead(lhs)
    val tpe = parseType()
    val sup = if kind == Tok.SubT then { advance(); Some(parseType(LvlBar)) }
    else None
    val defn = if kind == Tok.Eq then { advance(); Some(parseNonType(LvlSemi)) }
    else None
    expect(Tok.Period, "`.` after declaration")
    Decl(name, params, tpe, sup, defn, abbrev = false, fact = fact)(spanFrom(start))

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
        fail(
          "a rule name cannot start a declaration",
          "unexpected `:`",
          Some("rule names are written `@name head :- body.`; declarations have no `@`")
        )
      expect(Tok.Period, if body.isEmpty then "`.`, `,` or `:-`" else "`.` after rule body")
    else advance()
    Rule(name, heads.toList, body)(spanFrom(start))

  private def declHead(lhs: Tree): (Ident, List[Param]) =
    def flatten(t: Tree, acc: List[Tree]): (Tree, List[Tree]) = t match
      case Apply(f, a) => flatten(f, a :: acc)
      case other => (other, acc)
    val (hd, args) = flatten(lhs, Nil)
    val name = hd match
      case id: Ident => id
      case other =>
        reporter.report(
          Diagnostic.error("E0004", "malformed declaration head", other.span, "expected a lowercase name")
            .withNote("declarations have the form `name param* : type.` and definitions `name param* = expr.`")
        )
        throw new ParseError
    val params = args.map {
      case v: VarRef => Param.VarParam(v)
      case a @ Ascribe(n @ (_: Ident | _: VarRef), t) => Param.Typed(n, t, a.span)
      case other =>
        reporter.report(
          Diagnostic.error("E0004", "malformed parameter", other.span, "expected `X` or `(name : type)`")
        )
        throw new ParseError
    }
    (name, params)

  // ---------------------------------------------------------------- directives

  private def parsePath(): Tree =
    val t = advance()
    if t.kind != Tok.Name then
      i -= 1
      fail(s"expected a name, found $found", "expected a relation or path")
    var p: Tree = Ident(t.text)(t.span)
    while kind == Tok.Select do
      advance()
      val n = expect(Tok.Name)
      p = Select(p, n.text)(p.span.to(n.span), n.span)
    p

  private def parseModeItems(): List[ModeItem] =
    val b = mutable.ListBuffer.empty[ModeItem]
    while kind == Tok.Plus || kind == Tok.Minus do
      val t = advance()
      // `+e` names the column labelled `e`
      val lbl = if kind == Tok.Name then
        val n = advance(); Some(Ident(n.text)(n.span))
      else None
      b += ModeItem(t.kind == Tok.Plus, lbl, t.span.to(lbl.map(_.span).getOrElse(t.span)))
    b.toList

  private def parseDirective(): Item =
    val start = tok.span.start
    val d = advance()
    val kindName = d.text.drop(1)
    val args: DirArgs = kindName match
      case "abbrev" =>
        val lhs = parseExpr(LvlAdd)
        expect(Tok.Colon)
        val (name, params) = declHead(lhs)
        val tpe = parseType()
        expect(Tok.Eq, "`=` (an %abbrev must have a definition)")
        val defn = parseNonType(LvlSemi)
        expect(Tok.Period)
        return Decl(name, params, tpe, None, Some(defn), abbrev = true)(spanFrom(start))
      case "fact" =>
        // `%fact c : τ̄ -> a.`: a modifier of a constructor or struct declaration
        val lhs = parseExpr(LvlHead)
        if kind != Tok.Colon then
          fail(
            s"expected `:` after the name of a `%fact` declaration, found $found",
            "expected `:`",
            Some("`%fact` marks a constructor or struct declaration: `%fact c : int -> t.`")
          )
        return parseDeclRest(lhs, start, fact = true)
      case "mode" =>
        val p = parsePath()
        DirArgs.Mode(p, parseModeItems())
      case "terminates" =>
        // a measure: one variable or label, or a parenthesised tuple of them (lexicographic)
        val measure =
          if kind == Tok.LParen && (peekTok(1).kind == Tok.Var || peekTok(1).kind == Tok.Name) then
            advance()
            val first = advance()
            val b = mutable.ListBuffer(first)
            while kind == Tok.Comma do
              advance()
              b += expect(first.kind, if first.kind == Tok.Var then "a variable" else "a label")
            expect(Tok.RParen, "`)` after the measure")
            b.toList
          else if kind == Tok.Var || kind == Tok.Name then List(advance())
          else fail(s"expected a variable, a label or a parenthesised measure after %terminates, found $found")
        if measure.head.kind == Tok.Var then
          expect(Tok.LParen, "`(` followed by a call pattern")
          val p = parsePath()
          val args = mutable.ListBuffer.empty[Tree]
          while kind != Tok.RParen && kind != Tok.EOF && kind != Tok.Period do args += parsePostfix()
          expect(Tok.RParen)
          DirArgs.TerminatesVar(measure.map(v => VarRef(v.text)(v.span)), p, args.toList)
        else DirArgs.TerminatesLabel(measure.map(l => Ident(l.text)(l.span)), parsePath())
      case "open" | "input" | "output" => DirArgs.Target(parsePath())
      case "partial" =>
        reporter.report(Diagnostic.error("E0001", "`%partial` has been removed", d.span, "removed directive")
          .withNote("every accepted program terminates; there are no round budgets (docs/REDESIGN.md §4.6)")
          .withHelp("let an argument decrease along the recursion, bound it by a guard, or use a bound column (`min int` / `max int`)"))
        throw new ParseError
      case "derivations" =>
        if kind == Tok.RuleName then
          val r = advance()
          DirArgs.Target(RuleRef(r.text.drop(1))(r.span))
        else DirArgs.Target(parsePath())
      case "infix" =>
        val a = expect(Tok.Name, "`left`, `right` or `none`")
        if !Set("left", "right", "none")(a.text) then
          reporter.report(Diagnostic.error("E0001", s"unknown associativity `${a.text}`", a.span, "expected `left`, `right` or `none`"))
        val p = expect(Tok.IntLit, "a precedence")
        val n = expect(Tok.Name, "an operator name")
        DirArgs.Infix(a.text, p.value match { case l: Long => l.toInt; case _ => 0 }, Ident(n.text)(n.span))
      case "name" =>
        val p = parsePath()
        val v = expect(Tok.Var)
        DirArgs.NameHint(p, VarRef(v.text)(v.span))
      case "complete" =>
        reporter.report(Diagnostic.error("E0004", "`%complete` may only occur in a signature", d.span, "not allowed here")
          .withHelp("write it inside a record type, e.g. `{ edge : node -> node -> rel, %complete edge }`"))
        throw new ParseError
      case other =>
        reporter.report(Diagnostic.error("E0001", s"unknown directive `%$other`", d.span, "unknown directive")
          .withNote("directives are %mode %terminates %open %derivations %input %output %infix %name %abbrev %fact"))
        throw new ParseError
    expect(Tok.Period, "`.` after directive")
    Directive(kindName, args)(spanFrom(start), d.span)

  // ---------------------------------------------------------------- expressions

  private def infixAt(t: Token): Option[(String, Int, Assoc)] = t.kind match
    case Tok.Semi => Some((";", LvlSemi, Assoc.Left))
    case Tok.Comma => Some((",", LvlComma, Assoc.Left))
    case Tok.Arrow => Some(("->", LvlArrow, Assoc.Right))
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
            fail(s"operator `$op` is non-associative", "cannot chain this operator", Some("add parentheses"))
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
            case "->" =>
              lhs match
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
      case Tok.LBrack =>
        advance()
        val p = tok
        val param: Tree = p.kind match
          case Tok.Var => advance(); VarRef(p.text)(p.span)
          case Tok.Name => advance(); Ident(p.text)(p.span)
          case _ => fail(s"expected a lambda parameter, found $found", "expected a name or variable")
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
    case Tok.Name => !infixOps.contains(t.text)
    case _ => false
  )

  private def parseApp(): Tree =
    var f = parsePostfix()
    while startsArg(tok) do
      val a = parsePostfix()
      f = Apply(f, a)(f.span.to(a.span))
    f

  private def parsePostfix(): Tree =
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
              reporter.report(Diagnostic.error("E0003", "integer literal out of range", t.span, "does not fit into a 64-bit integer"))
              Lit(Literal.IntL(0))(t.span)
          case _ => Lit(Literal.IntL(0))(t.span)
      case Tok.FloatLit => advance(); Lit(Literal.FloatL(t.value.asInstanceOf[Double]))(t.span)
      case Tok.StrLit => advance(); Lit(Literal.StrL(t.value.asInstanceOf[String]))(t.span)
      case Tok.KwType => advance(); Keyword(Kw.Type)(t.span)
      case Tok.KwMod => advance(); Keyword(Kw.Mod)(t.span)
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
      case Tok.KwNot | Tok.Minus | Tok.LBrack => parsePrefix(LvlSemi)
      case Tok.Error => throw new ParseError
      case _ =>
        fail(s"expected an expression, found $found", "expected an expression")

  private def parseParens(): Tree =
    val start = tok.span.start
    advance()
    if kind == Tok.Var && peekTok(1).kind == Tok.KwWith then
      val v = advance()
      advance()
      if kind != Tok.LBrace then fail(s"expected `{` after `with`, found $found")
      val fields = parseBraces() match
        case RecordLit(fs, false) => fs
        case RecordLit(fs, true) =>
          reporter.report(Diagnostic.error("E0001", "`..` is not allowed in an update", tok.span))
          fs
        case ModuleBody(Nil) => Nil
        case other =>
          reporter.report(Diagnostic.error("E0001", "expected fields `{ l = t, ... }` after `with`", other.span))
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
        reporter.report(Diagnostic.error("E0001", "unclosed module body", Span(src, start, start + 1), "this `{` is never closed"))
        throw new ParseError
      advance()
      ModuleBody(items.toList)(spanFrom(start))

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

  private def parseRecordType(start: Int): Tree =
    val entries = mutable.ListBuffer.empty[SigEntry]
    var continue = true
    while continue do
      if kind == Tok.Directive && tok.text == "%complete" then
        val d = advance()
        val l = expect(Tok.Name, "a label")
        entries += SigEntry.Complete(Ident(l.text)(l.span), d.span.to(l.span))
      else if kind == Tok.Directive && tok.text == "%mode" then
        val d = advance()
        val l = expect(Tok.Name, "a label")
        val ms = parseModeItems()
        entries += SigEntry.ModeReq(Ident(l.text)(l.span), ms, d.span.to(ms.lastOption.map(_.span).getOrElse(l.span)))
      else
        val fact = kind == Tok.Directive && tok.text == "%fact"
        if fact then advance()
        val l = expect(Tok.Name, "a label")
        expect(Tok.Colon, "`:` in record type")
        entries += SigEntry.FieldDecl(Ident(l.text)(l.span), parseType(), fact)
      if kind == Tok.Comma then advance() else continue = false
    expect(Tok.RBrace, "`,` or `}`")
    RecordType(entries.toList)(spanFrom(start))

  private def parseRecordLit(start: Int): Tree =
    val fields = mutable.ListBuffer.empty[Field]
    var rest = false
    var continue = true
    while continue do
      if kind == Tok.DotDot then
        advance(); rest = true; continue = false
      else
        val l = expect(Tok.Name, "a label")
        expect(Tok.Eq, "`=` in record")
        fields += Field(Ident(l.text)(l.span), parseNonType(LvlArrow))
        if kind == Tok.Comma then advance() else continue = false
    expect(Tok.RBrace, if rest then "`}` after `..`" else "`,` or `}`")
    RecordLit(fields.toList, rest)(spanFrom(start))

object Parser:
  enum Assoc:
    case Left, Right, NonAssoc
  val LvlSemi = 10
  val LvlComma = 20
  val LvlArrow = 30
  val LvlBar = 40
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
