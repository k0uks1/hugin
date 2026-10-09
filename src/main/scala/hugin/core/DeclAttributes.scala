package hugin.core

import hugin.syntax.Literal
import hugin.util.Span

/** A term of a `%terminates` call pattern, as far as the object level needs it: the variable at a
 *  position, a literal, or any other term. */
enum PatternTerm:
  case Variable(name: Name)
  case Literal(value: hugin.syntax.Literal)
  case Other

/** An attribute of a declaration (reference: directives): what the primitive directives attach. */
enum Attribute(val directive: String):
  case Input extends Attribute("%input")
  case Output extends Attribute("%output")
  case Open extends Attribute("%open")
  case Derivations extends Attribute("%derivations")

  /** `%terminates`: measure variables (with the call pattern's terms) or column labels. */
  case Terminates(variables: Option[List[Name]], labels: List[Name], pattern: List[PatternTerm]) extends Attribute("%terminates")

/** What a value of type `decl` describes. */
enum DeclValue:
  /** `span`: the position of the data (the name it was quoted from), or of the directive. */
  case Constant(id: Int, attrs: List[Attribute], span: Span)
  case NamedRule(name: Name, attrs: List[Attribute])
  case Rejected(message: String)

/** Data of type `decl` that is not closed: the value as shown, and its position. */
final class OpenDeclData(val shown: String, val span: Span) extends Exception(shown, null, false, false)

/** Reads the values of the prelude's type `decl` (reference: directives): `dconst ⟨c⟩ attrs`, `drule "r" attrs`
 *  and `derror "message"`, with the attributes `ainput`, `aoutput`, `aopen`, `aderivations` and
 *  `aterminates m t̄`. The data must be closed (normalised in a closed environment); constructors are
 *  recognised by name, which is safe since the data has the prelude's type. */
final class DeclAttributes(core: Core):
  import core.*

  /** The declaration that a closed value of type `decl` describes; `fallback` is the position of the
   *  directive (for data without positions). */
  def decode(v: Val, fallback: Span): DeclValue = ctor(v, fallback) match
    case ("dconst", List(s, as), sp) =>
      val (id, at) = located(s, sp)
      DeclValue.Constant(id, list(as, sp).map(attribute(_, sp)), at)
    case ("drule", List(n, as), sp) => DeclValue.NamedRule(string(n, sp), list(as, sp).map(attribute(_, sp)))
    case ("derror", List(m), sp) => DeclValue.Rejected(string(m, sp))
    case (_, _, sp) => notClosed(v, sp)

  private def peel(v: Val, sp: Span): (Val, Span) = force(v) match
    case Val.Obj(ObjForm.Loc(s), List(x)) => peel(x, if s.exists then s else sp)
    case other => (other, sp)

  private def notClosed(v: Val, sp: Span): Nothing = throw OpenDeclData(showValPlain(Nil, v), sp)

  /** A constructor application: the constructor's name, its explicit arguments, its position. */
  private def ctor(v: Val, sp: Span): (Name, List[Val], Span) = peel(v, sp) match
    case (Val.Rigid(Head.Glob(id), spine), s) if globals(id).kind.isInstanceOf[GlobalKind.Constructor] =>
      (globals(id).name, spine.reverse.collect { case Elim.EApp(a, Icit.Expl) => a }, s)
    case (other, s) => notClosed(other, s)

  private def list(v: Val, sp: Span): List[Val] = ctor(v, sp) match
    case ("nil", Nil, _) => Nil
    case ("cons", List(x, xs), s) => x :: list(xs, s)
    case (_, _, s) => notClosed(v, s)

  private def string(v: Val, sp: Span): String = peel(v, sp) match
    case (Val.Lit(Literal.StrL(s), _), _) => s
    case (other, s) => notClosed(other, s)

  /** The object constant a symbol `⟨c⟩` refers to. */
  def symbol(v: Val, sp: Span): Int = located(v, sp)._1

  /** The object constant a symbol refers to, and the position of the symbol (or `sp`). */
  private def located(v: Val, sp: Span): (Int, Span) = peel(v, sp) match
    case (Val.Quote(x), s) =>
      peel(x, s) match
        case (Val.Rigid(Head.Glob(id), Nil), s2) => (id, s2)
        case (other, s2) => notClosed(other, s2)
    case (other, s) => notClosed(other, s)

  private def attribute(v: Val, sp: Span): Attribute = ctor(v, sp) match
    case ("ainput", Nil, _) => Attribute.Input
    case ("aoutput", Nil, _) => Attribute.Output
    case ("aopen", Nil, _) => Attribute.Open
    case ("aderivations", Nil, _) => Attribute.Derivations
    case ("aterminates", List(m, ts), s) =>
      val pattern = list(ts, s).map(term(_, s))
      ctor(m, s) match
        case ("mvars", List(vs), s2) => Attribute.Terminates(Some(list(vs, s2).map(string(_, s2))), Nil, pattern)
        case ("mlabels", List(ls), s2) => Attribute.Terminates(None, list(ls, s2).map(string(_, s2)), pattern)
        case (_, _, s2) => notClosed(m, s2)
    case (_, _, s) => notClosed(v, s)

  private def term(v: Val, sp: Span): PatternTerm = ctor(v, sp) match
    case ("tvar", List(n), s) => PatternTerm.Variable(string(n, s))
    case ("tint" | "tfloat" | "tstr", List(l), s) =>
      peel(l, s) match
        case (Val.Lit(lit, _), _) => PatternTerm.Literal(lit)
        case (other, s2) => notClosed(other, s2)
    case _ => PatternTerm.Other
