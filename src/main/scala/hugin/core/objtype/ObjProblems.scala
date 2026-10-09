package hugin.core
package objtype

import hugin.obj.{ArithOp, CmpOp, VarName}
import hugin.obj.DiagArgs.given
import hugin.syntax.AggKind
import hugin.util.{Origin, Span}
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** An object type in a message (printed by [[ObjTypes.show]]). */
final case class TyName(shown: String)

/** An object constant in a message. */
final case class ConstName(name: String)

given DiagArg[TyName] = DiagArg(t => Seg.Type(t.shown))
given DiagArg[ConstName] = DiagArg(c => Seg.Code(c.name))

/** Problems of object-level declarations and type inference (E0401–E0405). `where` describes a position
 *  in prose ("column 1 of `p`"), with code in backticks. */
enum ObjTypeError extends Problem:
  // ------------------------------------------------------------------- declarations (E0404)
  case CyclicRefinement(tpe: ConstName, at: Span)
  case RefinesNonBase(tpe: ConstName, base: TyName, at: Span)

  /** A subtyping edge `sub <: sup` whose member is not a fact type or an open type. */
  case NotOpenMember(sub: TyName, sup: ConstName, at: Span, edgeOrigin: Origin)
  case UnionMemberNotFacts(member: TyName, at: Span, declOrigin: Origin)
  case UnionOverlap(left: TyName, right: TyName, common: ConstName, at: Span, declOrigin: Origin)

  // ------------------------------------------------------------------------- rules (E0401–E0405)
  /** The expected types of a variable have no meet. `failed` is the occurrence where the meet became
   *  empty; `others` the other occurrences (one per type); `expected` every expectation in order. */
  case NoMeet(v: VarName, failed: (TyName, Span), others: List[(TyName, Span)], expected: List[(TyName, String)])
  case HeadNotAtom(at: Span)
  case Mismatch(found: TyName, expected: TyName, where: String, at: Span)
  case PatternNeverMatches(ctor: ConstName, column: TyName, where: String, at: Span)
  case UnaryMinus(operand: TyName, at: Span)
  case ArithOperands(op: ArithOp, left: TyName, right: TyName, at: Span)
  case Incomparable(op: CmpOp, left: TyName, right: TyName, at: Span)
  case AggregateOperand(kind: AggKind, operand: TyName, at: Span)

  /** An ascription `(t : T)` whose `T` does not select members of the type `inner` of `t`. */
  case AscriptionNotSelecting(tpe: TyName, inner: TyName, at: Span)
  case AscriptionNotTestable(at: Span)

  def code: Code = this match
    case _: CyclicRefinement | _: RefinesNonBase | _: NotOpenMember | _: UnionMemberNotFacts | _: UnionOverlap => Code.E0404
    case _: NoMeet => Code.E0401
    case _: AscriptionNotSelecting | _: AscriptionNotTestable => Code.E0405
    case _ => Code.E0402

  def primary: Span = this match
    case CyclicRefinement(_, s) => s
    case RefinesNonBase(_, _, s) => s
    case NotOpenMember(_, _, s, _) => s
    case UnionMemberNotFacts(_, s, _) => s
    case UnionOverlap(_, _, _, s, _) => s
    case NoMeet(_, (_, s), _, _) => s
    case HeadNotAtom(s) => s
    case Mismatch(_, _, _, s) => s
    case PatternNeverMatches(_, _, _, s) => s
    case UnaryMinus(_, s) => s
    case ArithOperands(_, _, _, s) => s
    case Incomparable(_, _, _, s) => s
    case AggregateOperand(_, _, s) => s
    case AscriptionNotSelecting(_, _, s) => s
    case AscriptionNotTestable(s) => s

  def message: Msg = this match
    case CyclicRefinement(t, _) => msg"cyclic refinement $t"
    case RefinesNonBase(t, b, _) => msg"$t refines $b, which is not a base type or refinement"
    case NotOpenMember(sub, sup, _, _) => msg"$sub cannot be a member of the open type $sup"
    case UnionMemberNotFacts(m, _, _) => msg"union member $m is not a type of facts"
    case UnionOverlap(l, r, _, _, _) => msg"union members $l and $r overlap"
    case _: NoMeet => msg"no value can occur in all these positions"
    case _: HeadNotAtom => msg"the head of a rule must be a relation atom"
    case _: Mismatch => msg"type mismatch"
    case _: PatternNeverMatches => msg"pattern can never match"
    case UnaryMinus(t, _) => msg"unary minus cannot be applied to $t"
    case ArithOperands(op, l, r, _) => msg"operator $op cannot be applied to $l and $r"
    case Incomparable(_, l, r, _) => msg"cannot compare $l with $r"
    case AggregateOperand(k, t, _) => msg"$k cannot aggregate values of type $t"
    case _: AscriptionNotSelecting | _: AscriptionNotTestable => msg"invalid ascription"

  override def primaryLabel: Msg = this match
    case _: NotOpenMember => msg"expected a fact type or an open type"
    case UnionOverlap(_, _, c, _, _) => msg"both contain $c"
    case NoMeet(v, (t, _), _, _) => msg"$v has type $t here"
    case Mismatch(found, expected, _, _) => msg"expected $expected, found $found"
    case PatternNeverMatches(c, ct, _, _) => msg"$c facts are not of type $ct"
    case Incomparable(op, _, _, _) => msg"$op on incompatible types"
    case AscriptionNotSelecting(tp, inner, _) => msg"$tp does not select members of $inner"
    case _: AscriptionNotTestable => msg"only types of facts can be tested at run time"
    case _ => Msg.empty

  override def labels: List[(Span, Msg)] = this match
    case NoMeet(v, _, others, _) => others.map((t, sp) => sp -> msg"$v has type $t here")
    case _ => Nil

  override def notes: List[Msg] = this match
    case _: UnionMemberNotFacts => List(msg"every type in a union must be a subtype of `rel`")
    case NoMeet(v, _, _, expected) =>
      val each = expected.map((t, w) => msg"$t (${Msg.text(w)})")
      List(msg"$v is expected to have type ${Msg.join(each, ", ")}")
    case Mismatch(_, _, w, _) => List(msg"in ${Msg.text(w)}")
    case PatternNeverMatches(_, _, w, _) => List(msg"in ${Msg.text(w)}")
    case _: ArithOperands =>
      List(msg"`+ - * /` apply to two ints or two floats, `^` to two strings; ints and floats are never converted")
    case Incomparable(op, _, _, _) =>
      List(
        if op == CmpOp.Eq || op == CmpOp.Ne then msg"both sides must have the same base type, or both be facts"
        else msg"ordering comparisons apply to two values of the same base type"
      )
    case AggregateOperand(k, _, _) =>
      List(if k == AggKind.Sum then msg"sum applies to int or float" else msg"${Lit(k.show)} applies to base types")
    case _: AscriptionNotSelecting => List(msg"an ascription (t : T) is a checked downcast; T must be a subtype of the type of t")
    case _ => Nil

  override def origin: Origin = this match
    case NotOpenMember(_, _, _, o) => o
    case UnionMemberNotFacts(_, _, o) => o
    case UnionOverlap(_, _, _, _, o) => o
    case _ => Origin.Source

/** Problems of projections and updates of records (E0303–E0305). */
enum RecordError extends Problem:
  case ProjectionOfNonVariable(at: Span)
  case UpdateOfNonVariable(at: Span)
  case ProjectionNotClosed(v: VarName, tpe: TyName, at: Span)
  case UpdateNotClosed(v: VarName, tpe: TyName, at: Span)

  /** `label` is not a column of the members `missing` of the type of a projected (`projected` = the
   *  variable and its type) or updated variable. */
  case NoCommonLabel(label: String, missing: List[ConstName], projected: Option[(VarName, TyName)], at: Span)

  /** The types of `label` in the members of the projected type (`columns`) have no join. */
  case UndefinedJoin(label: String, columns: List[(ConstName, TyName)], at: Span)

  def code: Code = this match
    case _: NoCommonLabel => Code.E0304
    case _: UndefinedJoin => Code.E0305
    case _ => Code.E0303

  def primary: Span = this match
    case ProjectionOfNonVariable(s) => s
    case UpdateOfNonVariable(s) => s
    case ProjectionNotClosed(_, _, s) => s
    case UpdateNotClosed(_, _, s) => s
    case NoCommonLabel(_, _, _, s) => s
    case UndefinedJoin(_, _, s) => s

  def message: Msg = this match
    case _: ProjectionOfNonVariable => msg"projection applies only to variables"
    case _: UpdateOfNonVariable => msg"update applies only to variables"
    case _: ProjectionNotClosed => msg"projection on a type that is not closed"
    case _: UpdateNotClosed => msg"update on a type that is not closed"
    case NoCommonLabel(l, _, _, _) => msg"no common label ${Src(l)}"
    case UndefinedJoin(l, _, _) => msg"undefined join for label ${Src(l)}"

  override def primaryLabel: Msg = this match
    case _: ProjectionOfNonVariable => msg"bind this term to a variable first"
    case ProjectionNotClosed(v, t, _) => msg"$v has type $t"
    case UpdateNotClosed(v, t, _) => msg"$v has type $t"
    case NoCommonLabel(_, missing, _, _) => msg"not a column of ${Msg.join(missing.map(m => msg"$m"), ", ")}"
    case UndefinedJoin(_, cs, _) => Msg.join(cs.map((c, ct) => msg"$ct in $c"), ", ")
    case _ => Msg.empty

  override def notes: List[Msg] = this match
    case _: ProjectionNotClosed =>
      List(msg"projection and update require a fact type or a union of fact types; open types may gain constructors")
    case NoCommonLabel(_, _, Some((v, t)), _) => List(msg"$v has type $t; every member must have the label")
    case _: UndefinedJoin => List(msg"the join of different base types is undefined")
    case _ => Nil
