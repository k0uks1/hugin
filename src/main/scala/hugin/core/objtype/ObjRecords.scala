package hugin.core
package objtype

import hugin.obj.VarName
import hugin.util.Span

/** Projections `X.l` and updates `(X with { l = h, … })` of facts (reference: object/types): the type of `X`
 *  must be closed, and every member must have the label (E0303–E0305). */
private object ObjRecords:
  def checkProj(chk: ObjCheck, types: ObjTypes, t: OTerm, x: String, l: String, col: Option[OTy], inHead: Boolean, where: String): Unit =
    chk.typeOfVar(x) match
      case Some(tx) if !tx.vague && !types.isAbstract(tx) =>
        if !types.isClosed(tx) then chk.problem(RecordError.ProjectionNotClosed(VarName(x), chk.tyName(tx), t.span))
        else
          types.commonLabel(tx, l) match
            case Left(missing) =>
              chk.problem(RecordError.NoCommonLabel(l, missing.map(m => ConstName(m.name)), Some((VarName(x), chk.tyName(tx))), t.span))
            case Right(cs) =>
              types.join(cs.map(_._3)) match
                case None => chk.problem(RecordError.UndefinedJoin(l, cs.map((c, _, ct) => (ConstName(c.name), chk.tyName(ct))), t.span))
                case Some(j) => col.foreach(ct => if inHead && !types.isSub(j, ct) then chk.mismatchAt(t, j, ct, where))
      case _ =>

  def checkWith(
      chk: ObjCheck,
      types: ObjTypes,
      t: OTerm,
      x: String,
      fields: List[(String, OTerm, Span)],
      col: Option[OTy],
      inHead: Boolean,
      where: String
  ): Unit =
    chk.typeOfVar(x) match
      case Some(tx) if !tx.vague && !types.isAbstract(tx) =>
        if !types.isClosed(tx) then chk.problem(RecordError.UpdateNotClosed(VarName(x), chk.tyName(tx), t.span))
        else
          for (l, h, sp) <- fields do
            types.commonLabel(tx, l) match
              case Left(missing) => chk.problem(RecordError.NoCommonLabel(l, missing.map(m => ConstName(m.name)), None, sp))
              case Right(cs) => for (c, _, ct) <- cs do chk.term(h, Some(ct), inHead = true, s"update of `$l` in `${c.name}`")
        col.foreach(ct => if inHead && !types.isSub(tx, ct) then chk.mismatchAt(t, tx, ct, where))
      case _ =>
