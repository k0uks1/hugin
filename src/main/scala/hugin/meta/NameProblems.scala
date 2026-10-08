package hugin.meta

import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** The problems of the namer (E0102, E0103 and the malformed clauses of E0004): declarations entered
 *  twice and items that cannot be classified by stage. Names are the declared names as written. */
enum NameError extends Problem:
  case Duplicate(name: String, at: Span, first: Span)
  case AbbrevNotTypeDefinition(at: Span)

  /** `%fact` on a declaration of a `kind` other than a constructor or struct. */
  case FactNotConstructor(name: String, kind: SymKind, at: Span)
  case RelationWithParameters(name: String, at: Span)
  case ClauseWithSeveralHeads(at: Span)
  case BaseTypeWithParameters(at: Span)
  case UnknownBaseType(name: String, at: Span, builtins: List[String])
  case StructWithSupertype(at: Span)
  case TypeDefinitionWithSupertype(at: Span)
  case SignatureWithoutDefinition(name: String, at: Span)
  case RelationDefinedByEquation(name: String, at: Span)

  /** A declaration `f : ... -> type` (a function returning a type), which is not a family. */
  case TypeFunction(name: String, at: Span)

  def code: Code = this match
    case _: Duplicate => Code.E0102
    case _: ClauseWithSeveralHeads => Code.E0004
    case _ => Code.E0103

  def primary: Span = this match
    case Duplicate(_, s, _) => s
    case AbbrevNotTypeDefinition(s) => s
    case FactNotConstructor(_, _, s) => s
    case RelationWithParameters(_, s) => s
    case ClauseWithSeveralHeads(s) => s
    case BaseTypeWithParameters(s) => s
    case UnknownBaseType(_, s, _) => s
    case StructWithSupertype(s) => s
    case TypeDefinitionWithSupertype(s) => s
    case SignatureWithoutDefinition(_, s) => s
    case RelationDefinedByEquation(_, s) => s
    case TypeFunction(_, s) => s

  def message: Msg = this match
    case Duplicate(n, _, _) => msg"${Src(n)} is declared twice in this scope"
    case _: AbbrevNotTypeDefinition => msg"`%abbrev` only applies to type definitions"
    case _: FactNotConstructor => msg"`%fact` only applies to constructor and struct declarations"
    case RelationWithParameters(n, _) => msg"relation ${Src(n)} cannot have parameters"
    case _: ClauseWithSeveralHeads => msg"a clause of a formula function must have exactly one head"
    case _: BaseTypeWithParameters => msg"a base type has no parameters or supertype"
    case UnknownBaseType(n, _, _) => msg"unknown base type ${Src(n)}"
    case _: StructWithSupertype => msg"a struct declaration cannot have a supertype"
    case _: TypeDefinitionWithSupertype => msg"a type definition cannot have a supertype"
    case SignatureWithoutDefinition(n, _) => msg"signature ${Src(n)} has no definition"
    case RelationDefinedByEquation(n, _) => msg"relation ${Src(n)} cannot be defined by `=`"
    case TypeFunction(n, _) => msg"cannot classify the declaration of ${Src(n)}"

  override def primaryLabel: Msg = this match
    case _: Duplicate => msg"redeclared here"
    case _: UnknownBaseType => msg"not a builtin"
    case _: TypeDefinitionWithSupertype => msg"remove this, or declare a refinement `a : type <: b.`"
    case _: RelationDefinedByEquation => msg"not allowed"
    case _: TypeFunction => msg"a function returning `type`"
    case _ => Msg.empty

  override def labels: List[(Span, Msg)] = this match
    case Duplicate(_, _, first) => List(first -> msg"first declared here")
    case _ => Nil

  override def notes: List[Msg] = this match
    case FactNotConstructor(n, k, _) => List(msg"${Src(n)} declares a ${Lit(k.describe)}")
    case UnknownBaseType(_, _, bs) => List(msg"the builtin base types are ${Lit(bs.mkString(", "))}")
    case _ => Nil

  override def helps: List[Msg] = this match
    case _: RelationWithParameters =>
      List(msg"type parameters of relation families are implicit: write uppercase type variables in the column types")
    case SignatureWithoutDefinition(n, _) => List(msg"write ${Src(s"$n : mod = { ... }.")}")
    case _: RelationDefinedByEquation => List(msg"relations are defined by rules: `c X :- body.`")
    case _: TypeFunction => List(msg"declare a family with type parameters instead: `f A : type.`")
    case _ => Nil
