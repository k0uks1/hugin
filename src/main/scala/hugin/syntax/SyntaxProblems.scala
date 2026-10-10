package hugin.syntax

import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** What the parser found where it expected something else. */
enum Found:
  case Token(text: String)
  case EndOfFile

object Found:
  given DiagArg[Found] = DiagArg {
    case Token(t) => Seg.Code(t)
    case EndOfFile => Seg.Text("end of file")
  }

/** Something the parser expected: a token, or a kind of syntax described in words ("an expression"). */
enum Expect:
  case Token(kind: Tok)
  case Thing(description: String)

  def msg: Msg = this match
    case Token(k) => Msg.text(Lexer.describe(k))
    case Thing(d) => Msg.text(d)

object Expect:
  val expression: Expect = Thing("an expression")
  val tpe: Expect = Thing("a type")
  val label: Expect = Thing("a label")
  val item: Expect = Thing("an item")
  val variable: Expect = Thing("a variable")
  val period: Expect = Token(Tok.Period)

  /** An expected set rendered as a list: "`.`, `,` or `:-`". */
  given DiagArg[List[Expect]] = es =>
    val ms = es.distinct.map(_.msg)
    val listed = if ms.length <= 1 then Msg.join(ms, "") else Msg.join(ms.init, ", ") ++ Msg.text(" or ") ++ ms.last
    listed.segs

/** The construct an error occurred in: its kind ("rule", "declaration") and its first token (shown as a
 *  secondary label when it is on an earlier line than the error). */
final case class Context(construct: String, start: Span)

/** A specific help for a common mistake, attached to an [[SyntaxError.Expected]]. */
enum SyntaxHelp:
  /** `::` in a declaration header (a type signature written as in Haskell). */
  case DoubleColon(at: Span)

  /** `:=` in a definition header: a declaration's type is missing. */
  case ColonEquals(colon: Span)

  /** `=` in a record type, or `:` in a record value. */
  case RecordSeparator(at: Span, inType: Boolean)

  /** A lowercase name where a variable is expected (after `as`, before `with`). */
  case LowercaseVariable(name: String, at: Span)

  /** `$` not followed by the expression of a hole or splice. */
  case DollarWithoutExpression

  /** `:-` in parentheses or a list: a rule as data, which is written in a quote `'( h :- b )`. */
  case RuleOutsideQuote(at: Span)

/** The problems of the lexer and the parser (E0001–E0005): the inventory of the syntax phase. */
enum SyntaxError extends Problem:
  // ---------------------------------------------------------------------------------------- lexer
  case UnterminatedComment(start: Span)
  case UnterminatedString(start: Span)

  /** A `%` or `@` not followed by a lowercase name. */
  case NameExpectedAfter(sigil: Char, at: Span)
  case UnexpectedCharacter(char: String, at: Span)
  case InvalidUnicodeEscape(hex: String, at: Span)
  case InvalidEscape(at: Span)
  case IntegerOutOfRange(at: Span)

  // --------------------------------------------------------------------------------------- parser
  /** One of `expected` was expected where `found` is. */
  case Expected(expected: List[Expect], found: Found, at: Span, context: Option[Context], help: Option[SyntaxHelp] = None)

  /** A missing `.` at the end of an item (`construct`), inserted at `at`, followed by the next item at
   *  `next`. */
  case MissingPeriod(construct: String, found: Found, at: Span, next: Option[Span])

  /** A delimiter `open` (at `openSpan`) that is not closed: `closer` is inserted at `at`, before `found`. */
  case Unclosed(open: String, openSpan: Span, closer: String, at: Span, found: Found, foundSpan: Span)
  case RuleNameOnDeclaration(at: Span)
  case NonAssociativeChain(op: String, at: Span)
  case UnmatchedBrace(at: Span)

  /** A closing delimiter in a construct over several lines that the construct goes on after, on its line,
   *  while its own closer follows (`[`⏎`1,`⏎`] 2`⏎`]`). */
  case StrayCloser(closer: String, at: Span)
  case UnknownAssociativity(name: String, at: Span)
  case RestInUpdate(at: Span)
  case ExpectedUpdateFields(at: Span)
  case MalformedDeclarationHead(at: Span)

  /** A declaration parameter that is neither `X` nor `(x : τ)`; `lowercase` if it is a lowercase name. */
  case MalformedParameter(at: Span, lowercase: Option[String] = None)
  case CompleteOutsideSignature(at: Span)

  /** `%partial`, which the redesign removed (every accepted program terminates). */
  case RemovedPartial(at: Span)

  /** A `where` keyword not followed by local definitions. */
  case EmptyWhere(at: Span)

  def code: Code = this match
    case _: UnterminatedComment | _: UnterminatedString => Code.E0002
    case _: InvalidUnicodeEscape | _: InvalidEscape | _: IntegerOutOfRange => Code.E0003
    case _: MalformedDeclarationHead | _: MalformedParameter | _: CompleteOutsideSignature => Code.E0004
    case _: Unclosed => Code.E0005
    case _ => Code.E0001

  def primary: Span = this match
    case UnterminatedComment(s) => s
    case UnterminatedString(s) => s
    case NameExpectedAfter(_, s) => s
    case UnexpectedCharacter(_, s) => s
    case InvalidUnicodeEscape(_, s) => s
    case InvalidEscape(s) => s
    case IntegerOutOfRange(s) => s
    case Expected(_, _, s, _, _) => s
    case MissingPeriod(_, _, s, _) => s
    case Unclosed(_, _, _, s, _, _) => s
    case RuleNameOnDeclaration(s) => s
    case NonAssociativeChain(_, s) => s
    case UnmatchedBrace(s) => s
    case StrayCloser(_, s) => s
    case UnknownAssociativity(_, s) => s
    case RestInUpdate(s) => s
    case ExpectedUpdateFields(s) => s
    case MalformedDeclarationHead(s) => s
    case MalformedParameter(s, _) => s
    case CompleteOutsideSignature(s) => s
    case RemovedPartial(s) => s
    case EmptyWhere(s) => s

  def message: Msg = this match
    case _: UnterminatedComment => msg"unterminated comment"
    case _: UnterminatedString => msg"unterminated string literal"
    case NameExpectedAfter(c, _) => msg"expected a lowercase name after ${Src(c.toString)}"
    case UnexpectedCharacter(c, _) => msg"unexpected character ${Src(c)}"
    case InvalidUnicodeEscape(hex, _) => msg"invalid unicode escape ${Src(s"\\u{$hex}")}"
    case _: InvalidEscape => msg"invalid escape sequence"
    case _: IntegerOutOfRange => msg"integer literal out of range"
    case Expected(_, f, _, _, Some(SyntaxHelp.DoubleColon(_))) => msg"expected `:` in a declaration, found $f"
    case Expected(_, f, _, _, Some(SyntaxHelp.LowercaseVariable(_, _))) => msg"expected a variable, found $f"
    case Expected(_, _, _, _, Some(SyntaxHelp.RuleOutsideQuote(_))) => msg"a rule outside a quote"
    case Expected(w, f, _, _, _) => msg"expected $w, found $f"
    case MissingPeriod(c, f, _, _) => msg"expected `.` after the ${Lit(c)}, found $f"
    case Unclosed(open, _, _, _, _, _) => msg"unclosed ${Src(open)}"
    case _: RuleNameOnDeclaration => msg"a rule name cannot start a declaration"
    case NonAssociativeChain(op, _) => msg"operator ${Src(op)} is non-associative"
    case _: UnmatchedBrace => msg"unmatched `}`"
    case StrayCloser(c, _) => msg"stray ${Src(c)}"
    case UnknownAssociativity(a, _) => msg"unknown associativity ${Src(a)}"
    case _: RestInUpdate => msg"`..` is not allowed in an update"
    case _: ExpectedUpdateFields => msg"expected fields `{ l = t, ... }` after `with`"
    case _: MalformedDeclarationHead => msg"malformed declaration head"
    case _: MalformedParameter => msg"malformed parameter"
    case _: CompleteOutsideSignature => msg"`%complete` may only occur in a signature"
    case _: RemovedPartial => msg"`%partial` has been removed"
    case _: EmptyWhere => msg"empty `where` block"

  override def primaryLabel: Msg = this match
    case _: UnterminatedComment => msg"comment starts here"
    case _: UnterminatedString => msg"string starts here"
    case _: InvalidUnicodeEscape => msg"not a Unicode scalar value"
    case _: InvalidEscape => Msg.text("valid escapes are \\\" \\\\ \\n \\t \\u{...}")
    case _: IntegerOutOfRange => msg"does not fit into a 64-bit integer"
    case Expected(_, _, _, _, Some(SyntaxHelp.DoubleColon(_))) => msg"expected `:`"
    case Expected(_, _, _, _, Some(SyntaxHelp.LowercaseVariable(_, _))) => msg"a name, not a variable"
    case Expected(_, _, _, _, Some(SyntaxHelp.RuleOutsideQuote(_))) => msg"`:-` outside a quote"
    case Expected(w, _, _, _, _) => msg"expected $w"
    case _: MissingPeriod => msg"expected `.` here"
    case Unclosed(_, _, closer, _, _, _) => msg"expected ${Src(closer)} here"
    case _: RuleNameOnDeclaration => msg"unexpected `:`"
    case _: NonAssociativeChain => msg"cannot chain this operator"
    case _: UnmatchedBrace => msg"no module body to close"
    case StrayCloser(c, _) => msg"the construct goes on after this ${Src(c)}, and is closed later"
    case _: UnknownAssociativity => msg"expected `left`, `right` or `none`"
    case _: MalformedDeclarationHead => msg"expected a lowercase name"
    case _: MalformedParameter => msg"expected `X` or `(name : type)`"
    case _: CompleteOutsideSignature => msg"not allowed here"
    case _: RemovedPartial => msg"removed directive"
    case _: EmptyWhere => msg"expected local definitions"
    case _ => Msg.empty

  override def labels: List[(Span, Msg)] = this match
    case Expected(_, _, _, Some(Context(construct, start)), _) =>
      List(start -> msg"this ${Lit(construct)} starts here")
    case MissingPeriod(_, _, _, next) => next.toList.map(_ -> msg"next item starts here")
    case Unclosed(open, openSpan, _, _, _, _) => List(openSpan -> msg"this ${Src(open)} is never closed")
    case _ => Nil

  override def notes: List[Msg] = this match
    case _: MalformedDeclarationHead =>
      List(msg"declarations have the form `name param* : type.` and definitions `name param* = expr.`")
    case _: RemovedPartial => List(msg"every accepted program terminates; there are no round budgets")
    case Expected(_, _, _, _, Some(SyntaxHelp.DoubleColon(_))) => List(msg"`::` is the list constructor of the meta level")
    case _ => Nil

  override def helps: List[Msg] = this match
    case Expected(_, _, _, _, Some(h)) =>
      h match
        case _: SyntaxHelp.DoubleColon => List(msg"declarations are written `name : type.`")
        case _: SyntaxHelp.ColonEquals => List(msg"a definition without a declared type is written `name = expr.`")
        case SyntaxHelp.RecordSeparator(_, true) =>
          List(msg"a record type declares its fields with `:`, a record value gives them with `=`")
        case SyntaxHelp.RecordSeparator(_, false) =>
          List(msg"a record value gives its fields with `=`, a record type declares them with `:`")
        case SyntaxHelp.LowercaseVariable(_, _) => List(msg"variables start with an uppercase letter or `_`")
        case SyntaxHelp.DollarWithoutExpression => List(msg"a hole or splice is written `$$x`, `$$(f x)`, `$$..xs` or `$$f[V]`")
        case _: SyntaxHelp.RuleOutsideQuote => List(msg"a rule as data is written in a quote: `'( h :- b )`")
    case _: MissingPeriod => List(msg"every item ends with a period")
    case _: RuleNameOnDeclaration => List(msg"rule names are written `@name head :- body.`; declarations have no `@`")
    case _: NonAssociativeChain => List(msg"add parentheses")
    case MalformedParameter(_, Some(_)) => List(msg"a parameter is a variable `X` or a typed parameter `(x : type)`")
    case _: RemovedPartial =>
      List(msg"let an argument decrease along the recursion, bound it by a guard, or use a bound column (`min int` / `max int`)")
    case _: CompleteOutsideSignature => List(msg"write it inside a record type, e.g. `{ edge : node -> node -> rel, %complete edge }`")
    case _ => Nil

  override def suggestions: List[Suggestion] = this match
    case MissingPeriod(_, _, at, _) => List(Suggestion.replace(at, ".", msg"add `.`", Applicability.MachineApplicable))
    case Unclosed(_, _, closer, at, _, _) =>
      List(Suggestion.replace(at, closer, msg"add ${Src(closer)}", Applicability.MachineApplicable))
    case MalformedParameter(at, Some(name)) =>
      val v = name.capitalize
      List(Suggestion.replace(at, v, msg"write the variable ${Src(v)}", Applicability.MaybeIncorrect))
    case Expected(_, _, _, _, Some(h)) =>
      h match
        case SyntaxHelp.DoubleColon(at) => List(Suggestion.replace(at, ":", msg"replace `::` with `:`", Applicability.MachineApplicable))
        case SyntaxHelp.ColonEquals(colon) => List(Suggestion.replace(colon, "", msg"remove `:`", Applicability.MachineApplicable))
        case SyntaxHelp.RecordSeparator(at, inType) =>
          val (bad, good) = if inType then ("=", ":") else (":", "=")
          List(Suggestion.replace(at, good, msg"replace ${Src(bad)} with ${Src(good)}", Applicability.MaybeIncorrect))
        case SyntaxHelp.LowercaseVariable(name, at) =>
          val v = name.capitalize
          List(Suggestion.replace(at, v, msg"write the variable ${Src(v)}", Applicability.MaybeIncorrect))
        case SyntaxHelp.DollarWithoutExpression | _: SyntaxHelp.RuleOutsideQuote => Nil
    case _ => Nil
