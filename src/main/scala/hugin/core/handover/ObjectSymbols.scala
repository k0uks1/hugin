package hugin.core
package handover

import hugin.obj.{Column, OType, RelKind, RelSym, TypeKind, TypeSym}
import hugin.util.*
import scala.collection.mutable

/** The object symbols of a program's object constants: one [[TypeSym]] per object type, one [[RelSym]]
 *  per relation, constructor and struct, with their columns and result types translated from the core.
 *
 *  The declared constants get their symbols first, in the order of their declarations in the source
 *  ([[declare]]; the object level orders the members of a closed type by symbol id); instances of
 *  families get theirs when the staged program first refers to them, so only the instances it uses are
 *  part of it. A symbol's declaration is filled in after it exists, since declarations may refer to each
 *  other in any order. */
final class ObjectSymbols(core: Core, reporter: Reporter):
  import core.*

  private val types = mutable.LinkedHashMap.empty[Int, TypeSym]
  private val rels = mutable.LinkedHashMap.empty[Int, RelSym]

  /** The symbols of the families, which instances name as what they instantiate (for display). */
  private val familyTypes = mutable.HashMap.empty[Int, TypeSym]
  private val familyRels = mutable.HashMap.empty[Int, RelSym]

  /** Creates the symbols of the object constants among `ids` (in this order). */
  def declare(ids: List[Int]): Unit = ids.foreach(symbolOf)

  def allTypes: Vector[TypeSym] = types.values.toVector
  def allRelations: Vector[RelSym] = rels.values.toVector

  /** The instances of family `fam` that the staged program uses so far, in the order of first use. */
  def instancesOf(fam: Int): List[Int] =
    (types.keys ++ rels.keys).filter(id => globals(id).instanceOf.exists(_._1 == fam)).toList

  /** All instances the staged program uses so far. */
  def instanceIds: List[Int] = (types.keys ++ rels.keys).filter(id => globals(id).instanceOf.isDefined).toList

  def typeSym(id: Int): Option[TypeSym] = symbolOf(id).collect { case t: TypeSym => t }
  def relSym(id: Int): Option[RelSym] = symbolOf(id).collect { case r: RelSym => r }

  private def symbolOf(id: Int): Option[TypeSym | RelSym] =
    types.get(id).orElse(rels.get(id)).orElse {
      globals(id).kind match
        case GlobalKind.Object(d) => Some(create(id, d))
        case _ => None
    }

  private def create(id: Int, d: ObjDecl): TypeSym | RelSym =
    val g = globals(id)
    d match
      case ObjDecl.OpenType | ObjDecl.Refinement(_) =>
        val t = TypeSym(g.name, TypeKind.Open, g.declSpan, Origin.Source)
        types(id) = t
        for (fam, args) <- g.instanceOf do
          t.instanceOf = Some((familyTypes.getOrElseUpdate(fam, TypeSym(globals(fam).name, TypeKind.Open, t.span, Origin.Source)), Nil))
        fillType(id, t)
        t
      case _ =>
        val r = RelSym(g.name, relKind(d), g.declSpan, Origin.Source, fact(d))
        rels(id) = r
        for (fam, _) <- g.instanceOf do
          r.instanceOf = Some((familyRels.getOrElseUpdate(fam, RelSym(globals(fam).name, r.kind, r.span, Origin.Source, r.fact)), Nil))
        fillRelation(id, r)
        r

  private def relKind(d: ObjDecl): RelKind = d match
    case ObjDecl.Constructor(_) => RelKind.Ctor
    case ObjDecl.Struct(_) => RelKind.Struct
    case _ => RelKind.Plain

  private def fact(d: ObjDecl): Boolean = d match
    case ObjDecl.Constructor(f) => f
    case ObjDecl.Struct(f) => f
    case _ => false

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
    case Tm.Global(id) if typeSym(id).isDefined => OType.Con(typeSym(id).get, Nil)
    case Tm.FactTy(r) =>
      Tm.unloc(r) match
        case Tm.Global(id) if relSym(id).isDefined => OType.Fact(relSym(id).get, Nil)
        case other => notAnObjectType(other, span)
    case Tm.Obj(ObjForm.Union, ms) => OType.union(ms.map(otype(_, span)))
    case other => notAnObjectType(other, span)

  private def notAnObjectType(t: Tm, span: Span): OType =
    reporter.report(elab.ElabProblem.StuckObjectType(showTm(Nil, t), span).toDiagnostic)
    OType.Err
