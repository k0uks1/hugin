package hugin.runtime

import hugin.obj.{BaseType, OType}
import hugin.obj.DiagArgs.given
import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** Problems of loading input facts (E0801). Names are relation or constructor names as written; `arities`
 *  are the arities the program declares for a name. */
enum InputError extends Problem:
  case LiteralMismatch(expected: OType, found: BaseType, at: Span)
  case NotGround(at: Span)
  case ExpectedConstructorTerm(at: Span)
  case ConstructorMisplaced(name: String, expected: OType, arities: List[Int], at: Span)
  case UnknownConstructor(name: String, at: Span)
  case AmbiguousConstructor(name: String, expected: OType, at: Span)
  case ExpectedFact(at: Span)
  case NotInputRelation(name: String, at: Span)
  case RelationArity(name: String, arities: List[Int], at: Span)
  case UnknownRelation(name: String, at: Span)
  case AmbiguousRelation(name: String, at: Span)
  case NotAFact(at: Span)

  def code: Code = Code.E0801

  def primary: Span = this match
    case LiteralMismatch(_, _, s) => s
    case NotGround(s) => s
    case ExpectedConstructorTerm(s) => s
    case ConstructorMisplaced(_, _, _, s) => s
    case UnknownConstructor(_, s) => s
    case AmbiguousConstructor(_, _, s) => s
    case ExpectedFact(s) => s
    case NotInputRelation(_, s) => s
    case RelationArity(_, _, s) => s
    case UnknownRelation(_, s) => s
    case AmbiguousRelation(_, s) => s
    case NotAFact(s) => s

  def message: Msg = this match
    case _: LiteralMismatch => msg"type mismatch in input fact"
    case _: NotGround => msg"input facts must be ground"
    case _: ExpectedConstructorTerm => msg"expected a constructor term"
    case ConstructorMisplaced(n, _, _, _) => msg"${Src(n)} cannot occur here"
    case UnknownConstructor(n, _) => msg"unknown constructor ${Src(n)}"
    case AmbiguousConstructor(n, _, _) => msg"ambiguous constructor ${Src(n)}"
    case _: ExpectedFact => msg"expected a fact `rel arg ...`"
    case NotInputRelation(n, _) => msg"${Src(n)} is not an input relation"
    case RelationArity(n, as, _) => msg"${Src(n)} expects ${arities(as)} argument(s)"
    case UnknownRelation(n, _) => msg"unknown relation ${Src(n)}"
    case AmbiguousRelation(n, _) => msg"ambiguous relation ${Src(n)}"
    case _: NotAFact => msg"input files contain only ground facts"

  override def primaryLabel: Msg = this match
    case LiteralMismatch(e, f, _) => msg"expected $e, found ${Src(f.show)}"
    case _: NotGround => msg"variable in input fact"
    case ConstructorMisplaced(_, e, _, _) => msg"expected a value of type $e"
    case _: UnknownConstructor | _: UnknownRelation => msg"not declared in the program"
    case AmbiguousConstructor(_, e, _) => msg"several instances fit $e"
    case _: NotInputRelation => msg"facts can only be loaded into input relations"
    case _: NotAFact => msg"not a fact"
    case _ => Msg.empty

  override def helps: List[Msg] = this match
    case ConstructorMisplaced(n, _, as, _) => List(msg"${Src(n)} takes ${arities(as)} argument(s)")
    case NotInputRelation(n, _) => List(msg"declare ${Src(s"%input $n.")} in the program")
    case _ => Nil

  private def arities(as: List[Int]): Lit = Lit(as.mkString(" or "))
