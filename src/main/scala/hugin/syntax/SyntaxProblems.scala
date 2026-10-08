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

/** The problems of the lexer and the parser (E0001–E0004): the inventory of the syntax phase. */
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
  /** `what` was expected (a description such as "`.` after rule body"). */
  case Expected(what: Msg, found: Found, at: Span, label: Msg, help: Option[Msg] = None)

  /** A missing `.` at the end of an item that is followed by the next item on a later line. */
  case MissingPeriod(what: Msg, found: Found, at: Span, next: Span)
  case RuleNameOnDeclaration(at: Span)
  case NonAssociativeChain(op: String, at: Span)
  case UnmatchedBrace(at: Span)
  case UnclosedModuleBody(open: Span)
  case UnknownAssociativity(name: String, at: Span)
  case UnknownDirective(name: String, at: Span)
  case RestInUpdate(at: Span)
  case ExpectedUpdateFields(at: Span)
  case MalformedDeclarationHead(at: Span)
  case MalformedParameter(at: Span)
  case CompleteOutsideSignature(at: Span)

  /** `%partial`, which the redesign removed (every accepted program terminates). */
  case RemovedPartial(at: Span)

  def code: Code = this match
    case _: UnterminatedComment | _: UnterminatedString => Code.E0002
    case _: InvalidUnicodeEscape | _: InvalidEscape | _: IntegerOutOfRange => Code.E0003
    case _: MalformedDeclarationHead | _: MalformedParameter | _: CompleteOutsideSignature => Code.E0004
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
    case RuleNameOnDeclaration(s) => s
    case NonAssociativeChain(_, s) => s
    case UnmatchedBrace(s) => s
    case UnclosedModuleBody(s) => s
    case UnknownAssociativity(_, s) => s
    case UnknownDirective(_, s) => s
    case RestInUpdate(s) => s
    case ExpectedUpdateFields(s) => s
    case MalformedDeclarationHead(s) => s
    case MalformedParameter(s) => s
    case CompleteOutsideSignature(s) => s
    case RemovedPartial(s) => s

  def message: Msg = this match
    case _: UnterminatedComment => msg"unterminated comment"
    case _: UnterminatedString => msg"unterminated string literal"
    case NameExpectedAfter(c, _) => msg"expected a lowercase name after ${Src(c.toString)}"
    case UnexpectedCharacter(c, _) => msg"unexpected character ${Src(c)}"
    case InvalidUnicodeEscape(hex, _) => msg"invalid unicode escape ${Src(s"\\u{$hex}")}"
    case _: InvalidEscape => msg"invalid escape sequence"
    case _: IntegerOutOfRange => msg"integer literal out of range"
    case Expected(w, f, _, _, _) => msg"expected $w, found $f"
    case MissingPeriod(w, f, _, _) => msg"expected $w, found $f"
    case _: RuleNameOnDeclaration => msg"a rule name cannot start a declaration"
    case NonAssociativeChain(op, _) => msg"operator ${Src(op)} is non-associative"
    case _: UnmatchedBrace => msg"unmatched `}`"
    case _: UnclosedModuleBody => msg"unclosed module body"
    case UnknownAssociativity(a, _) => msg"unknown associativity ${Src(a)}"
    case UnknownDirective(d, _) => msg"unknown directive ${Src("%" + d)}"
    case _: RestInUpdate => msg"`..` is not allowed in an update"
    case _: ExpectedUpdateFields => msg"expected fields `{ l = t, ... }` after `with`"
    case _: MalformedDeclarationHead => msg"malformed declaration head"
    case _: MalformedParameter => msg"malformed parameter"
    case _: CompleteOutsideSignature => msg"`%complete` may only occur in a signature"
    case _: RemovedPartial => msg"`%partial` has been removed"

  override def primaryLabel: Msg = this match
    case _: UnterminatedComment => msg"comment starts here"
    case _: UnterminatedString => msg"string starts here"
    case _: InvalidUnicodeEscape => msg"not a Unicode scalar value"
    case _: InvalidEscape => Msg.text("valid escapes are \\\" \\\\ \\n \\t \\u{...}")
    case _: IntegerOutOfRange => msg"does not fit into a 64-bit integer"
    case Expected(_, _, _, label, _) => label
    case _: MissingPeriod => msg"expected `.` here"
    case _: RuleNameOnDeclaration => msg"unexpected `:`"
    case _: NonAssociativeChain => msg"cannot chain this operator"
    case _: UnmatchedBrace => msg"no module body to close"
    case _: UnclosedModuleBody => msg"this `{` is never closed"
    case _: UnknownAssociativity => msg"expected `left`, `right` or `none`"
    case _: UnknownDirective => msg"unknown directive"
    case _: MalformedDeclarationHead => msg"expected a lowercase name"
    case _: MalformedParameter => msg"expected `X` or `(name : type)`"
    case _: CompleteOutsideSignature => msg"not allowed here"
    case _: RemovedPartial => msg"removed directive"
    case _ => Msg.empty

  override def labels: List[(Span, Msg)] = this match
    case MissingPeriod(_, _, _, next) => List(next -> msg"next item starts here")
    case _ => Nil

  override def notes: List[Msg] = this match
    case _: MalformedDeclarationHead =>
      List(msg"declarations have the form `name param* : type.` and definitions `name param* = expr.`")
    case _: UnknownDirective =>
      List(msg"directives are %mode %terminates %open %derivations %input %output %infix %name %abbrev %fact")
    case _: RemovedPartial => List(msg"every accepted program terminates; there are no round budgets")
    case _ => Nil

  override def helps: List[Msg] = this match
    case Expected(_, _, _, _, help) => help.toList
    case _: MissingPeriod => List(msg"every item ends with a period")
    case _: RuleNameOnDeclaration => List(msg"rule names are written `@name head :- body.`; declarations have no `@`")
    case _: NonAssociativeChain => List(msg"add parentheses")
    case _: RemovedPartial =>
      List(msg"let an argument decrease along the recursion, bound it by a guard, or use a bound column (`min int` / `max int`)")
    case _: CompleteOutsideSignature => List(msg"write it inside a record type, e.g. `{ edge : node -> node -> rel, %complete edge }`")
    case _ => Nil

  override def suggestions: List[Suggestion] = this match
    case MissingPeriod(_, _, at, _) => List(Suggestion.replace(at, ".", msg"add `.`", Applicability.MachineApplicable))
    case _ => Nil
