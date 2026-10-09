package hugin.core
package objtype

import hugin.obj.{ArithOp, CmpOp}
import hugin.syntax.{AggKind, Literal}
import hugin.util.Span

/** Object code as the object type system checks it: the terms and formulas of a rule, query or piece of
 *  object code, with the object constants resolved to their columns ([[RelInfo]]). Built from core terms
 *  by [[ObjWalk]], during elaboration and after staging. */
enum OTerm:
  case Var(name: String, span: Span)
  case Lit(l: Literal, span: Span)

  /** Code whose structure the checker does not see (spliced meta code, a persisted value), of a type. */
  case Code(ty: OTy, span: Span)

  /** An application of a relation, constructor or struct (`None` for a head the core does not know). */
  case App(rel: Option[RelInfo], args: List[OTerm], span: Span)
  case As(t: OTerm, v: String, span: Span)
  case Ascr(t: OTerm, ty: OTy, span: Span)
  case Proj(t: OTerm, label: String, span: Span)
  case With(t: OTerm, fields: List[(String, OTerm, Span)], span: Span)
  case Arith(op: ArithOp, l: OTerm, r: OTerm, span: Span)
  case Neg(t: OTerm, span: Span)

  def span: Span

enum OFormula:
  case Atom(rel: RelInfo, args: List[OTerm], as: Option[String], span: Span)
  case Cmp(op: CmpOp, l: OTerm, r: OTerm, span: Span)
  case Not(f: OFormula, span: Span)
  case Agg(res: String, kind: AggKind, t: OTerm, body: List[OFormula], span: Span)
  case Disj(alts: List[List[OFormula]], span: Span)

  /** A term at a position of a known type that is not a column of an atom: an argument of a meta function
   *  that takes object code (`cheap X` passes `X` as `⇑item`). In a head it is checked as a column. */
  case Expect(t: OTerm, ty: OTy, where: String, span: Span)

  def span: Span
