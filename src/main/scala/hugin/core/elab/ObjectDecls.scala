package hugin.core
package elab

import hugin.syntax.Tree
import hugin.syntax.Trees.*
import hugin.util.*

/** Declarations of object constants beyond `x : A.` (REDESIGN §3.1): structs `s : type = { l : τ, … }.`,
 *  refinements `a : type <: b.`, subtyping edges `τ <: a.`, and the classification of a declared object
 *  constant ([[ObjDecl]]). The core records what they declare; whether the subtyping makes sense is
 *  checked by the object typer on the staged program. */
trait ObjectDecls:
  self: Elaborator =>
  import core.*

  /** The kind of an object constant declared `x : A.` with the (closed) object type `ty`. */
  def objectDecl(d: Decl, ty: Val): ObjDecl = force(ty) match
    case Val.U0 => ObjDecl.OpenType
    case other => if isRelationType(other) then ObjDecl.Relation else ObjDecl.Constructor(d.fact)

  def isStructDecl(d: Decl): Boolean = (d.tpe, d.defn) match
    case (Keyword(Kw.Type), Some(_: RecordType)) => d.params.isEmpty
    case _ => false

  /** `s : type = { l₁ : τ₁, … }.`: the relation `s : (l₁ : τ₁) -> … -> rel`, whose fact type is `s`. */
  def elabStruct(d: Decl): Unit =
    val entries = d.defn.get.asInstanceOf[RecordType].entries
    val fields = entries.map {
      case SigEntry.FieldDecl(l, t, fact) =>
        if fact then error("E0004", "`%fact` is not allowed on the fields of a struct", l.span, "struct field")
        (l, t)
      case SigEntry.Complete(_, sp) => error("E0004", "requirements are not allowed in struct declarations", sp)
      case SigEntry.ModeReq(_, _, sp) => error("E0004", "requirements are not allowed in struct declarations", sp)
    }
    dupLabels(fields.map(_._1))
    val ty = columnsType(Cxt.empty, fields.map((l, t) => (l.name, t)), Tm.RelT)
    declare(d.name, ty, Stage.S0, GlobalKind.Object(ObjDecl.Struct(d.fact)), d.span)

  /** `(l₁ : τ₁) -> … -> result` over object column types (labels are not in scope: object arrows are not
   *  dependent). */
  def columnsType(c: Cxt, cols: List[(Name, Tree)], result: Tm): Tm = cols match
    case Nil => Tm.shift(result, c.lvl)
    case (l, t) :: rest =>
      val dt = columnType(c, t)
      Tm.Pi(l, Icit.Expl, dt, columnsType(newBinder(c, l, ev(c, dt), Stage.S0), rest, result))

  /** The type of a column: an object type, or a bound column type `min τ` / `max τ` (REDESIGN §5.2,
   *  validated at the object level by `obj/check/BoundColumns`). */
  def columnType(c: Cxt, t: Tree): Tm = t match
    case Parens(i) => columnType(c, i)
    case BoundType(k, inner) => Tm.Obj(ObjForm.BoundCol(k), List(check(c, inner, Val.U0, Stage.S0)))
    case _ => check(c, t, Val.U0, Stage.S0)

  /** `a : type <: b.` */
  def elabRefinement(d: Decl): Unit =
    d.tpe match
      case Keyword(Kw.Type) if d.params.isEmpty && d.defn.isEmpty =>
        val base = check(Cxt.empty, d.sup.get, Val.U0, Stage.S0)
        declare(d.name, Tm.U0, Stage.S0, GlobalKind.Object(ObjDecl.Refinement(zonk(Nil, 0, base))), d.span)
      case _ =>
        error("E0404", "only object types can be declared as refinements", d.sup.get.span, "`<:` after a type that is not `type`")

  /** `τ <: a.`: the object type `τ` (an object type, a relation's or constructor's fact type) becomes a
   *  subtype of the open type `a`. */
  def elabEdge(e: SubEdge): Unit =
    val sub = check(Cxt.empty, e.sub, Val.U0, Stage.S0)
    val sup = check(Cxt.empty, e.sup, Val.U0, Stage.S0)
    force(eval(Nil, sup)) match
      case Val.Rigid(Head.Glob(id), Nil) if globals(id).kind == GlobalKind.Object(ObjDecl.OpenType) =>
      case Val.Rigid(Head.Glob(id), Nil) if globals(id).stage == Stage.S0 =>
        fail(
          Diagnostic.error("E0404", s"`${globals(id).name}` is not an open type", e.sup.span, "edge target must be open")
            .withLabel(globals(id).span, "declared here")
        )
      case _ => error("E0404", "the target of a subtyping edge must be an open type", e.sup.span)
    items += CoreItem.EdgeItem(zonk(Nil, 0, sub), zonk(Nil, 0, sup), e.span)
