package hugin.core
package elab

import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** A meta function that an operator denotes (`%infix + plus.`): its name and type, as shown. */
final case class OperatorCandidate(name: String, tpe: String)

/** The problems of operators bound to meta functions (reference: lexical-structure, operators bound to
 *  meta functions) and of names that `%use` opens for several meta constants (reference: modules,
 *  overloaded opened names; #186 P9e): several bindings or declarations fit (E0932), or none does
 *  (E0933). Types are given as shown to users. */
enum OperatorProblem extends Problem:
  /** `a op b` where the bindings `fitting` all fit; `operand` is the type of the operand that was
   *  compared with them, if it is known. */
  case Ambiguous(op: String, fitting: List[OperatorCandidate], operand: Option[String], at: Span)

  /** `a op b` where none of the bindings `candidates` in scope fits: `operand` is the type of the operand
   *  that was compared with them and `expected` the expected type, where known. No candidates: the
   *  operator denotes no meta function in this scope (`≡` without `std/eq`, or in object code). */
  case NoneFits(op: String, candidates: List[OperatorCandidate], operand: Option[String], expected: Option[String], at: Span)

  /** A name that `%use` items open for several meta constants (#186 P9e), used where the constants
   *  `fitting` all fit; `operand` is the type of the first argument that was compared with them, if it is
   *  known; `uses` are the `%use` items that open it (E0932). */
  case AmbiguousName(name: String, fitting: List[OperatorCandidate], operand: Option[String], at: Span, uses: List[Span])

  /** A name that `%use` items open for several meta constants, used where none of them fits: applied to
   *  `args` explicit arguments, with `operand` the type of the first argument and `expected` the expected
   *  type, where known (E0933). */
  case NoNameFits(
      name: String,
      candidates: List[OperatorCandidate],
      operand: Option[String],
      expected: Option[String],
      args: Int,
      at: Span,
      uses: List[Span]
  )

  /** `p op q` in a pattern, where `op` denotes only the functions `names`, no constructor (E0915). */
  case NotAPattern(op: String, names: List[String], at: Span)

  def code: Code = this match
    case _: Ambiguous => Code.E0932
    case _: NoneFits => Code.E0933
    case _: NotAPattern => Code.E0915
    case _: AmbiguousName => Code.E0932
    case _: NoNameFits => Code.E0933

  def primary: Span = this match
    case AmbiguousName(_, _, _, s, _) => s
    case NoNameFits(_, _, _, _, _, s, _) => s
    case Ambiguous(_, _, _, s) => s
    case NoneFits(_, _, _, _, s) => s
    case NotAPattern(_, _, s) => s

  def message: Msg = this match
    case Ambiguous(op, _, _, _) => msg"ambiguous operator ${Src(op)}"
    case NoneFits(op, Nil, _, _, _) => msg"the operator ${Src(op)} denotes no meta function here"
    case NoneFits(op, _, _, _, _) => msg"no meta function that ${Src(op)} denotes fits here"
    case NotAPattern(op, _, _) => msg"the operator ${Src(op)} in a pattern denotes no constructor"
    case AmbiguousName(n, _, _, _, _) => msg"ambiguous name ${Src(n)}: several of the declarations that `%use` opens it for fit"
    case NoNameFits(n, _, _, _, _, _, _) => msg"none of the declarations that `%use` opens ${Src(n)} for fits here"

  override def primaryLabel: Msg = this match
    case Ambiguous(_, fs, _, _) => Msg.text(s"${fs.length} bindings fit")
    case NoneFits(_, Nil, _, _, _) => msg"not bound"
    case NoneFits(_, _, Some(t), _, _) => msg"an operand has type ${Src(t)}"
    case NoneFits(_, _, None, Some(t), _) => msg"expected ${Src(t)}"
    case NotAPattern(_, ns, _) => Msg.text(s"denotes ${ns.map(n => s"`$n`").mkString(", ")}, not a constructor")
    case AmbiguousName(_, fs, _, _, _) => Msg.text(s"${fs.length} declarations fit")
    case NoNameFits(_, _, Some(t), _, _, _, _) => msg"the first argument has type ${Src(t)}"
    case NoNameFits(_, _, None, Some(t), _, _, _) => msg"expected ${Src(t)}"
    case NoNameFits(_, _, None, None, k, _, _) => Msg.text(s"applied to $k explicit argument${if k == 1 then "" else "s"}")
    case _ => Msg.empty

  override def labels: List[(Span, Msg)] = this match
    case AmbiguousName(n, _, _, _, uses) => uses.map(_ -> msg"opens ${Src(n)}")
    case NoNameFits(n, _, _, _, _, _, uses) => uses.map(_ -> msg"opens ${Src(n)}")
    case _ => Nil

  override def notes: List[Msg] = this match
    case AmbiguousName(n, fs, operand, _, _) =>
      operand.map(t => msg"the first argument has type ${Src(t)}").toList ++
        fs.map(f => msg"${Src(n)} denotes ${Src(f.name + " : " + f.tpe)}")
    case NoNameFits(n, cs, operand, expected, _, _, _) =>
      (if operand.isDefined then expected.map(t => msg"the expected type is ${Src(t)}").toList else Nil) ++
        cs.map(f => msg"${Src(n)} denotes ${Src(f.name + " : " + f.tpe)}")
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
    case _: AmbiguousName =>
      List(
        msg"give the expected type, `(e : T)`, or the type of the first argument, or open only one of them, `%use m (…)` with a list of names"
      )
    case NoNameFits(n, _, _, _, _, _, _) =>
      List(msg"apply ${Src(n)} as the type of one of its declarations says, or open only the one meant, `%use m (…)` with a list of names")
    case Ambiguous(_, fs, _, _) =>
      List(Msg.text(
        s"give the type of an operand, `(x : T)`, or apply one of the functions by name: ${fs.map(f => s"`${f.name}`").mkString(", ")}"
      ))
    case NoneFits("≡", Nil, _, _, _) => List(msg"add `%use \"std/eq\".` to the file for `≡`, the equality `eq`")
    case NoneFits(_, Nil, _, _, _) => List(msg"bind the operator with `%infix op f.` in the file that declares `f`")
    case _ => Nil
