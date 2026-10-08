package hugin.core
package handover

import hugin.obj.{Column, OType, RelKind, RelSym, TypeKind, TypeSym}
import hugin.util.*
import scala.collection.mutable

/** The object symbols of a program's object constants: one [[TypeSym]] per object type, one [[RelSym]]
 *  per relation, constructor and struct, with their columns and result types translated from the core.
 *
 *  Symbols are created in the order of their declarations in the source (`symbols` must be called with
 *  the globals in that order before anything else asks for them): the object level orders the members
 *  of a closed type by symbol id. Their types are filled in after all symbols exist, since declarations
 *  may refer to each other in any order. */
final class ObjectSymbols(core: Core, reporter: Reporter):
  import core.*

  private val types = mutable.LinkedHashMap.empty[Int, TypeSym]
  private val rels = mutable.LinkedHashMap.empty[Int, RelSym]

  /** Creates the symbols of the object constants among `ids` (in this order), then their declarations. */
  def declare(ids: List[Int]): Unit =
    for id <- ids do
      globals(id).kind match
        case GlobalKind.Object(d) => create(id, d)
        case _ =>
    for (id, t) <- types do fillType(id, t)
    for (id, r) <- rels do fillRelation(id, r)

  def allTypes: Vector[TypeSym] = types.values.toVector
  def allRelations: Vector[RelSym] = rels.values.toVector

  def typeSym(id: Int): Option[TypeSym] = types.get(id)
  def relSym(id: Int): Option[RelSym] = rels.get(id)

  private def create(id: Int, d: ObjDecl): Unit =
    val g = globals(id)
    d match
      case ObjDecl.OpenType | ObjDecl.Refinement(_) => types(id) = TypeSym(g.name, TypeKind.Open, g.declSpan, Origin.Source)
      case ObjDecl.Relation => rels(id) = RelSym(g.name, RelKind.Plain, g.declSpan, Origin.Source)
      case ObjDecl.Constructor(fact) => rels(id) = RelSym(g.name, RelKind.Ctor, g.declSpan, Origin.Source, fact)
      case ObjDecl.Struct(fact) => rels(id) = RelSym(g.name, RelKind.Struct, g.declSpan, Origin.Source, fact)

  private def fillType(id: Int, t: TypeSym): Unit = globals(id).kind match
    case GlobalKind.Object(ObjDecl.Refinement(base)) => t.kind = TypeKind.Refinement(otype(nf(Nil, base), t.span))
    case _ =>

  private def fillRelation(id: Int, r: RelSym): Unit =
    val (cols, result) = columns(nf(Nil, globals(id).tyTm), r.span)
    r.cols = cols.toVector
    r.result = if r.kind == RelKind.Ctor then Some(otype(result, r.span)) else None

  /** The columns of an object arrow (labels `_` are unlabelled columns) and its result. */
  private def columns(ty: Tm, span: Span): (List[Column], Tm) = Tm.unloc(ty) match
    case Tm.Pi(x, _, dom, cod) =>
      val (rest, res) = columns(cod, span)
      (column(if x == "_" then None else Some(x), dom, span) :: rest, res)
    case other => (Nil, other)

  private def column(label: Option[Name], ty: Tm, span: Span): Column = Tm.unloc(ty) match
    case Tm.Obj(ObjForm.BoundCol(k), List(inner)) => Column(label, otype(inner, span), Some(k))
    case other => Column(label, otype(other, span))

  /** The object type a closed normal form denotes. */
  def otype(t: Tm, span: Span): OType = Tm.unloc(t) match
    case Tm.Base(b, Stage.S0) => OType.Base(b)
    case Tm.Global(id) if types.contains(id) => OType.Con(types(id), Nil)
    case Tm.FactTy(r) =>
      Tm.unloc(r) match
        case Tm.Global(id) if rels.contains(id) => OType.Fact(rels(id), Nil)
        case other => notAnObjectType(other, span)
    case Tm.Obj(ObjForm.Union, ms) => OType.union(ms.map(otype(_, span)))
    case other => notAnObjectType(other, span)

  private def notAnObjectType(t: Tm, span: Span): OType =
    reporter.report(
      Diagnostic.error("E0909", "cannot compute an object type at compile time", span, s"`${showTm(Nil, t)}` is not an object type")
        .withNote("the meta code that computes this type is stuck, so no object type results")
    )
    OType.Err
