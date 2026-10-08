package hugin.core
package elab

import hugin.syntax.Tree
import hugin.syntax.Trees.*
import hugin.util.*
import hugin.util.diagnostics.{Code as DiagCode, Legacy}

/** Records: record types with dependent fields (a telescope: later fields may mention earlier labels),
 *  record values, projections — also of object facts by column label (`I.price` for `I : item` where
 *  `item : (name : string) -> (price : int) -> rel`). Modules will be record values and signatures record
 *  types (REDESIGN §6.7). */
trait Records:
  self: Elaborator =>
  import core.*

  def dupLabels(ls: List[Ident]): Unit =
    ls.groupBy(_.name).collectFirst { case (_, xs) if xs.length > 1 => xs(1) }.foreach { l =>
      error(DiagCode.E0307, s"duplicate label `${l.name}`", l.span, "label used twice")
    }

  /** `{ l₁ : A₁, … }` checked against `Type l`: every field type is in `Type l`. */
  def checkRecordType(c: Cxt, entries: List[SigEntry], l: Level): Tm =
    val fields = entries.map {
      case SigEntry.FieldDecl(lb, tpe, _) => (lb, tpe)
      case SigEntry.Complete(_, sp) => unsupportedAt(sp, "`%complete` requirements")
      case SigEntry.ModeReq(_, _, sp) => unsupportedAt(sp, "`%mode` requirements")
    }
    dupLabels(fields.map(_._1))
    var cc = c
    Tm.RecTy(fields.map { (lb, tpe) =>
      val ft = check(cc, tpe, Val.U1(l), Stage.S1)
      cc = bind(cc, lb.name, ev(cc, ft), Stage.S1)
      (lb.name, ft)
    })

  /** A record value with an inferred (non-dependent) record type. */
  def inferRecord(c: Cxt, fields: List[Field]): (Tm, Val, Stage) =
    dupLabels(fields.map(_.label))
    val parts = fields.map(f => (f.label.name, inferS(c, f.value, Stage.S1)))
    // field j's type lives under j telescope binders: quoting at the deeper level shifts it
    val tys = parts.zipWithIndex.map { case ((l, (_, ty)), j) => (l, quote(c.lvl + j, ty)) }
    (Tm.Rec(parts.map((l, p) => (l, p._1))), ev(c, Tm.RecTy(tys)), Stage.S1)

  /** A record value checked against a record type: exactly its fields, each against its type
   *  instantiated with the earlier fields' values. */
  def checkRecord(c: Cxt, t: Tree, fields: List[Field], rt: Val.RecTy): Tm =
    dupLabels(fields.map(_.label))
    val byLabel = fields.map(f => f.label.name -> f).toMap
    fields.find(f => !rt.labels.contains(f.label.name)).foreach { f =>
      fail(
        Legacy.error(DiagCode.E0906, s"no field `${f.label.name}` in the expected record type", f.label.span, "unknown field")
          .withNote(s"the expected record type has the fields ${showLabels(rt.labels)}")
      )
    }
    rt.labels.find(l => !byLabel.contains(l)).foreach { l =>
      error(DiagCode.E0906, s"missing field `$l`", t.span, s"the field `$l` is missing")
    }
    var e = rt.env
    Tm.Rec(rt.labels.zip(rt.tys).map { (lb, ty) =>
      val ft = check(c, byLabel(lb).value, eval(e, ty), Stage.S1)
      e = ev(c, ft) :: e
      (lb, ft)
    })

  /** `q.l`: a projection of a meta record, or of an object fact by column label. */
  def inferSelect(c: Cxt, sel: Select): (Tm, Val, Stage) =
    val (qt, qty, qs) = spliceIfLifted(insertAll(c, sel.qual.span, infer(c, sel.qual)))
    qty match
      case rt: Val.RecTy =>
        fieldType(rt, ev(c, qt), sel.name) match
          case Some(fty) => (Tm.Proj(qt, sel.name), fty, qs)
          case None => noField(c, sel, qty, rt.labels)
      case Val.FactTy(r) =>
        columns(r).find(_._1 == sel.name) match
          case Some((_, cty)) => (Tm.Proj(qt, sel.name), cty, Stage.S0)
          case None => noField(c, sel, qty, columns(r).map(_._1).filter(_ != "_"))
      case other =>
        fail(
          Legacy.error(DiagCode.E0906, s"no field `${sel.name}`", sel.nameSpan, "unknown field")
            .withLabel(sel.qual.span, s"this has type `${show(c, other)}`, which is not a record type")
        )

  /** Object code `⇑A` is projected at the object level. */
  private def spliceIfLifted(r: (Tm, Val, Stage)): (Tm, Val, Stage) = force(r._2) match
    case Val.Lift(x) => (Tm.splice(r._1), force(x), Stage.S0)
    case other => (r._1, other, r._3)

  private def showLabels(ls: List[Name]): String = ls.map(l => s"`$l`").mkString(", ")

  private def noField(c: Cxt, sel: Select, ty: Val, labels: List[Name]): Nothing =
    fail(
      Legacy.error(DiagCode.E0906, s"no field `${sel.name}`", sel.nameSpan, "unknown field")
        .withNote(s"`${show(c, ty)}` has the fields ${showLabels(labels)}")
    )

  /** The labelled columns of an object relation (object arrows are not dependent, so the column types
   *  are closed). */
  def columns(r: Val): List[(Name, Val)] =
    def go(ty: Val, k: Int): List[(Name, Val)] = force(ty) match
      case Val.Pi(x, _, d, cl) => (x, d) :: go(inst(cl, Val.Wild), k + 1)
      case _ => Nil
    force(r) match
      case Val.Rigid(Head.Glob(id), Nil) => go(globals(id).ty, 0)
      case _ => Nil
