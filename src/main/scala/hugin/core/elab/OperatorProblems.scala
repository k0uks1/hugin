package hugin.core
package elab

import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** A meta function that an operator denotes (`%infix + plus.`): its name and type, as shown. */
final case class OperatorCandidate(name: String, tpe: String)

/** The problems of operators bound to meta functions (reference: lexical-structure, operators bound to
 *  meta functions): several bindings fit (E0932), or none does (E0933). Types are given as shown to
 *  users. */
enum OperatorProblem extends Problem:
  /** `a op b` where the bindings `fitting` all fit; `operand` is the type of the operand that was
   *  compared with them, if it is known. */
  case Ambiguous(op: String, fitting: List[OperatorCandidate], operand: Option[String], at: Span)

  /** `a op b` where none of the bindings `candidates` in scope fits: `operand` is the type of the operand
   *  that was compared with them and `expected` the expected type, where known. No candidates: the
   *  operator denotes no meta function in this scope (`≡` without `std/eq`, or in object code). */
  case NoneFits(op: String, candidates: List[OperatorCandidate], operand: Option[String], expected: Option[String], at: Span)

  /** `p op q` in a pattern, where `op` denotes only the functions `names`, no constructor (E0915). */
  case NotAPattern(op: String, names: List[String], at: Span)

  def code: Code = this match
    case _: Ambiguous => Code.E0932
    case _: NoneFits => Code.E0933
    case _: NotAPattern => Code.E0915

  def primary: Span = this match
    case Ambiguous(_, _, _, s) => s
    case NoneFits(_, _, _, _, s) => s
    case NotAPattern(_, _, s) => s

  def message: Msg = this match
    case Ambiguous(op, _, _, _) => msg"ambiguous operator ${Src(op)}"
    case NoneFits(op, Nil, _, _, _) => msg"the operator ${Src(op)} denotes no meta function here"
    case NoneFits(op, _, _, _, _) => msg"no meta function that ${Src(op)} denotes fits here"
    case NotAPattern(op, _, _) => msg"the operator ${Src(op)} in a pattern denotes no constructor"

  override def primaryLabel: Msg = this match
    case Ambiguous(_, fs, _, _) => Msg.text(s"${fs.length} bindings fit")
    case NoneFits(_, Nil, _, _, _) => msg"not bound"
    case NoneFits(_, _, Some(t), _, _) => msg"an operand has type ${Src(t)}"
    case NoneFits(_, _, None, Some(t), _) => msg"expected ${Src(t)}"
    case NotAPattern(_, ns, _) => Msg.text(s"denotes ${ns.map(n => s"`$n`").mkString(", ")}, not a constructor")
    case _ => Msg.empty

  override def notes: List[Msg] = this match
    case Ambiguous(op, fs, operand, _) =>
      operand.map(t => msg"an operand has type ${Src(t)}").toList ++
        fs.map(f => msg"${Src(op)} denotes ${Src(f.name + " : " + f.tpe)}")
    case _: NotAPattern =>
      List(msg"a pattern is built from constructors and variables, so an operator in a pattern must denote a constructor")
    case NoneFits(_, Nil, _, _, _) =>
      List(
        msg"an operator symbol denotes the meta functions that `%infix` binds it to in the files whose names are in scope; object code compares with `=`"
      )
    case NoneFits(op, cs, operand, expected, _) =>
      (if operand.isDefined then expected.map(t => msg"the expected type is ${Src(t)}").toList else Nil) ++
        cs.map(f => msg"${Src(op)} denotes ${Src(f.name + " : " + f.tpe)}")

  override def helps: List[Msg] = this match
    case Ambiguous(_, fs, _, _) =>
      List(Msg.text(
        s"give the type of an operand, `(x : T)`, or apply one of the functions by name: ${fs.map(f => s"`${f.name}`").mkString(", ")}"
      ))
    case NoneFits("≡", Nil, _, _, _) => List(msg"add `%use \"std/eq\".` to the file for `≡`, the equality `eq`")
    case NoneFits(_, Nil, _, _, _) => List(msg"bind the operator with `%infix op f.` in the file that declares `f`")
    case _ => Nil
