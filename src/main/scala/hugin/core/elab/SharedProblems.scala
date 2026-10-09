package hugin.core
package elab

import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** The problems of shared data declarations (reference: meta/families, shared data): the restrictions
 *  that make a declaration `T ā : data.` exist at both stages. A constructor argument that does not exist
 *  at both stages (E0920); a constructor that does not use its type at the parameters (E0921); a subtyping
 *  edge into a shared type (E0922); a shared declaration or constructor out of place (E0923). */
enum SharedProblem extends Problem:
  /** An argument type of constructor `ctor` of `family` that is not a parameter, a base type or a shared
   *  type. */
  case NotShareable(ctor: String, family: String, tpe: String, at: Span)

  /** A constructor of `family` whose result or recursive argument is not `family` at its parameters
   *  (`why`: what it is instead), or a declaration whose parameters are not variables. */
  case NotUniform(family: String, why: String, at: Span)

  /** `sub <: family` or `a : type <: family`. */
  case EdgeIntoShared(family: String, at: Span, declared: Span)

  /** `T ā : data.` in a module body or a `where` block. */
  case NotTopLevel(at: Span)

  /** A constructor of the shared type `family` declared outside the file that declares it. */
  case ConstructorElsewhere(ctor: String, family: String, at: Span, declared: Span)

  def code: Code = this match
    case _: NotShareable => Code.E0920
    case _: NotUniform => Code.E0921
    case _: EdgeIntoShared => Code.E0922
    case _: NotTopLevel | _: ConstructorElsewhere => Code.E0923

  def primary: Span = this match
    case NotShareable(_, _, _, s) => s
    case NotUniform(_, _, s) => s
    case EdgeIntoShared(_, s, _) => s
    case NotTopLevel(s) => s
    case ConstructorElsewhere(_, _, s, _) => s

  def message: Msg = this match
    case NotShareable(c, f, t, _) => msg"the constructor ${Src(c)} of the shared type ${Src(f)} has an argument of type ${Src(t)}"
    case NotUniform(f, _, _) => msg"the shared type ${Src(f)} must be used at its parameters"
    case EdgeIntoShared(f, _, _) => msg"a subtyping edge into the shared type ${Src(f)}"
    case _: NotTopLevel => msg"a shared data declaration that is not at the top level of a file"
    case ConstructorElsewhere(c, f, _, _) => msg"${Src(c)} declares a constructor of the shared type ${Src(f)} outside its file"

  override def primaryLabel: Msg = this match
    case _: NotShareable => msg"not a parameter, a base type or a shared type"
    case NotUniform(_, why, _) => Msg.text(why)
    case _: EdgeIntoShared => msg"a shared type is closed"
    case _: NotTopLevel => msg"`data` is only allowed here at the top level"
    case _: ConstructorElsewhere => msg"a constructor of a closed type"

  override def labels: List[(Span, Msg)] = this match
    case EdgeIntoShared(f, _, d) => List((d, msg"${Src(f)} is declared here"))
    case ConstructorElsewhere(_, f, _, d) => List((d, msg"${Src(f)} and its constructors are declared here"))
    case _ => Nil

  override def notes: List[Msg] = this match
    case _: NotShareable =>
      List(
        msg"a shared type exists at both stages, so the arguments of its constructors must exist at both: its parameters, `int`, `float`, `string` and shared types",
        msg"functions, universes, object code `⇑A`, `sym`, relations, meta types and object types that are not shared exist at one stage only"
      )
    case _: NotUniform =>
      List(
        msg"every constructor of a shared type `T ā` returns `T ā`, with the parameters as written in the declaration, and uses `T` only at `ā`: no indices and no polymorphic recursion, which the object level cannot represent"
      )
    case _: EdgeIntoShared | _: ConstructorElsewhere =>
      List(msg"the constructors of a shared type are fixed by its file: its meta side is an inductive family, whose clauses cover exactly these constructors")
    case _: NotTopLevel =>
      List(msg"the meta side of a shared type declared in a module body or a functor would be generative, which the meta level does not support")

  override def helps: List[Msg] = this match
    case NotShareable(_, _, t, _) =>
      List(msg"declare ${Src(t)} with `: data` as well, or declare this type as an object type (`: type`) or a meta type (`: Type`)")
    case _: EdgeIntoShared | _: ConstructorElsewhere =>
      List(msg"declare the constructor with the shared type, or declare an object type (`: type`) that is open")
    case _: NotTopLevel => List(msg"move the declaration and its constructors to the top level of the file")
    case _ => Nil
