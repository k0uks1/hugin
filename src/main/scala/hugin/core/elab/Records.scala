package hugin.core
package elab

import hugin.syntax.Tree
import hugin.syntax.Trees.*
import hugin.util.*

/** Records: record types with dependent fields (a telescope: later fields may mention earlier labels),
 *  record values, projections — also of object facts by column label (`I.price` for `I : item` where
 *  `item : (name : string) -> (price : int) -> rel`). Modules will be record values and signatures record
 *  types (reference: modules). */
trait Records:
  self: Elaborator =>
  import core.*

  /** E0307: a label used twice (in a named pattern, an update or a struct's columns). */
  def dupLabels(ls: List[Ident]): Unit = firstDuplicate(ls).foreach((l, first) => fail(ElabProblem.DuplicateLabel(l.name, l.span, first)))

  /** E0307: a field used twice in a record value or a signature. */
  def dupFields(ls: List[Ident], inSignature: Boolean): Unit =
    firstDuplicate(ls).foreach((l, _) => fail(ElabProblem.DuplicateField(l.name, inSignature, l.span)))

  private def firstDuplicate(ls: List[Ident]): Option[(Ident, Span)] =
    val seen = scala.collection.mutable.HashMap.empty[Name, Span]
    ls.collectFirst(Function.unlift { l =>
      seen.get(l.name) match
        case Some(first) => Some((l, first))
        case None =>
          seen(l.name) = l.span
          None
    })

  /** `{ l₁ : A₁, … }` checked against `Type l`: every field type is in `Type l`. A field whose type is
   *  the type of an object constant (`node : type`, `edge : node -> node -> rel`, `dot : shape`,
   *  `square : int -> shape`) is object code of that type, as a declaration would declare an object
   *  constant; other field types are meta types. Requirements (`%complete l`) are part of the record type ([[SigReq]]). */
  def checkRecordType(c: Cxt, entries: List[SigEntry], l: Level): Tm =
    val fields = entries.collect { case SigEntry.FieldDecl(lb, tpe) => (lb, tpe) }
    dupFields(fields.map(_._1), inSignature = true)
    var cc = c
    val tys = fields.map { (lb, tpe) =>
      val ft = signatureFieldType(cc, tpe, l)
      cc = bind(cc, lb.name, ev(cc, ft), Stage.S1)
      (lb.name, ft)
    }
    Tm.RecTy(tys, entries.flatMap(requirement(fields.map(_._1.name))), fields.map((lb, tpe) => (lb.span, lb.span.to(tpe.span))))

  private def signatureFieldType(c: Cxt, tpe: Tree, l: Level): Tm =
    val inferred =
      try Some(undoOnFailure(inferU(c, tpe)))
      catch case _: ElabError => None
    inferred match
      case Some((t, Stage.S0, _)) if isObjectConstantType(ev(c, t)) => Tm.Lift(t)
      case _ => check(c, tpe, Val.U1(l), Stage.S1)

  private def requirement(labels: List[Name])(e: SigEntry): Option[SigReq] = e match
    case SigEntry.FieldDecl(_, _) => None
    case SigEntry.Complete(lb, sp) => Some(SigReq.Complete(knownLabel(labels, lb), sp))

  private def knownLabel(labels: List[Name], lb: Ident): Name =
    if !labels.contains(lb.name) then fail(ElabProblem.UnknownRequirementField(lb.name, lb.span))
    lb.name

  /** A record value with an inferred (non-dependent) record type. */
  def inferRecord(c: Cxt, fields: List[Field]): (Tm, Val, Stage) =
    dupFields(fields.map(_.label), inSignature = false)
    val parts = fields.map(f => (f.label.name, inferS(c, f.value, Stage.S1)))
    // field j's type lives under j telescope binders: quoting at the deeper level shifts it
    val tys = parts.zipWithIndex.map { case ((l, (_, ty)), j) => (l, quote(c.lvl + j, ty)) }
    (Tm.Rec(parts.map((l, p) => (l, p._1))), ev(c, Tm.RecTy(tys)), Stage.S1)

  /** A record value checked against a record type: exactly its fields, each against its type
   *  instantiated with the earlier fields' values. */
  def checkRecord(c: Cxt, t: Tree, fields: List[Field], rt: Val.RecTy): Tm =
    dupFields(fields.map(_.label), inSignature = false)
    val byLabel = fields.map(f => f.label.name -> f).toMap
    fields.find(f => !rt.labels.contains(f.label.name)).foreach { f =>
      fail(TypeProblem.UnknownExpectedField(f.label.name, rt.labels, f.label.span))
    }
    rt.labels.find(l => !byLabel.contains(l)).foreach { l =>
      fail(ElabProblem.MissingSignatureField(l, show(c, rt), t.span))
    }
    var e = rt.env
    Tm.Rec(rt.labels.zip(rt.tys).map { (lb, ty) =>
      val ft = check(c, byLabel(lb).value, eval(e, ty), Stage.S1)
      e = ev(c, ft) :: e
      (lb, ft)
    })

  /** `q.l`: a projection of a meta record, or of an object fact by column label. */
  def inferSelect(c: Cxt, sel: Select): (Tm, Val, Stage) =
    val (qt, qty, qs) = spliceIfLifted(sel.qual.span, insertAll(c, sel.qual.span, infer(c, sel.qual)))
    qty match
      case rt: Val.RecTy =>
        fieldType(rt, ev(c, qt), sel.name) match
          case Some(fty) =>
            recordFieldUse(c, rt, sel, fty)
            (Tm.Proj(qt, sel.name), fty, qs)
          case None => noField(c, sel, qty, rt.labels)
      case _ if qs == Stage.S0 => objectProjection(c, sel, qt, qty)
      case other if qs == Stage.S1 && sel.qual.isInstanceOf[Ident] =>
        fail(ElabProblem.NotAModule(hugin.syntax.Printer.show(sel.qual), show(c, other), sel.qual.span))
      case other =>
        fail(TypeProblem.NotARecord(sel.name, sel.qual.span, show(c, other), sel.nameSpan))

  /** Object code `⇑A` is projected at the object level (spliced at the qualifier's position). */
  private def spliceIfLifted(span: Span, r: (Tm, Val, Stage)): (Tm, Val, Stage) = force(r._2) match
    case Val.Lift(x) => (located(span, Tm.splice(r._1), x, Stage.S0), force(x), Stage.S0)
    case other => (r._1, other, r._3)

  private def showLabels(ls: List[Name]): String = ls.map(l => s"`$l`").mkString(", ")

  private def noField(c: Cxt, sel: Select, ty: Val, labels: List[Name]): Nothing =
    if droppedImport(sel.qual, sel.name) then
      throw ElabError(ElabProblem.UnresolvedName(sel.name, sel.nameSpan, None, false).toDiagnostic, silent = true)
    fail(TypeProblem.NoField(sel.name, show(c, ty), labels, similarName(sel.name, labels), sel.nameSpan))

  /** The labelled columns of an object relation (object arrows are not dependent, so the column types
   *  are closed). */
  def columns(r: Val): List[(Name, Val)] =
    def go(ty: Val, k: Int): List[(Name, Val)] = force(ty) match
      case Val.Pi(x, _, d, cl) => (x, d) :: go(inst(cl, Val.Wild), k + 1)
      case _ => Nil
    force(r) match
      case Val.Rigid(Head.Glob(id), Nil) => go(globals(id).ty, 0)
      case _ => Nil
