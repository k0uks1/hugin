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
final class ObjectSymbols(core: Core, reporter: Reporter, val index: hugin.compiler.SemanticIndex = hugin.compiler.SemanticIndex()):
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
        val t = TypeSym(objectName(id), TypeKind.Open, g.declSpan, Origin.Source)
        types(id) = t
        for (fam, args) <- g.instanceOf do
          t.instanceOf = Some((familyTypes.getOrElseUpdate(fam, TypeSym(objectName(fam), TypeKind.Open, t.span, Origin.Source)), Nil))
        fillType(id, t)
        for (fam, args) <- g.instanceOf if d == ObjDecl.OpenType do closeInstance(fam, args)
        t
      case _ =>
        val r = RelSym(objectName(id), relKind(d), g.declSpan, Origin.Source)
        rels(id) = r
        for (fam, _) <- g.instanceOf do
          r.instanceOf = Some((familyRels.getOrElseUpdate(fam, RelSym(objectName(fam), r.kind, r.span, Origin.Source)), Nil))
        fillRelation(id, r)
        val base = g.instanceOf.map(_._1).getOrElse(id)
        r.derivedFrom = core.derivedFrom(base).map((o, _) => globals(o).instanceOf.map(i => globals(i._1)).getOrElse(globals(o)).name)
        r

  /** An instance of an open type family is closed with the instances of its constructors at the same
   *  arguments (`some[int]` with `option[int]`), so that input facts can use them. */
  private def closeInstance(fam: Int, args: List[Tm]): Unit =
    for c <- constructorsOf(fam) do
      familyInstance(c, args.map(eval(Nil, _))).foreach(v =>
        Val.unloc(force(v)) match
          case Val.Quote(q) =>
            Val.unloc(force(q)) match
              case Val.Rigid(Head.Glob(inst), Nil) => symbolOf(inst)
              case _ =>
          case _ =>
      )

  /** The constructor families of the type family `fam` whose parameters are the type's (`some : A -> option A`). */
  private def constructorsOf(fam: Int): List[Int] =
    val arity = globals(fam).kind match
      case GlobalKind.Family(_, n) => n
      case _ => 0
    globals.indices.toList.filter { c =>
      globals(c).kind match
        case GlobalKind.Family(ObjDecl.Constructor, `arity`) => resultIsFamily(c, fam, arity)
        case _ => false
    }

  /** Whether the constructor family `c`'s result is `fam` applied to `c`'s parameters, in order. */
  private def resultIsFamily(c: Int, fam: Int, arity: Int): Boolean =
    def result(ty: Val, k: Int): Val = force(ty) match
      case Val.Pi(_, _, _, cl) => result(inst(cl, Val.local(k)), k + 1)
      case other => other
    val params = (0 until arity).toList
    force(result(globals(c).ty, 0)) match
      case Val.Lift(t) =>
        Val.unloc(force(result(t, arity))) match
          case Val.Rigid(Head.Glob(`fam`), sp) =>
            sp.reverse.collect { case Elim.EApp(a, _) => a }.map(a => Val.unloc(force(a))) ==
              params.map(Val.local)
          case _ => false
      case _ => false

  /** The names of the object constants declared outside the prelude. */
  private lazy val ownNames: Set[Name] =
    globals.filter(g => !fromPrelude(g) && g.instanceOf.isEmpty && isObjectLike(g.kind)).map(_.name).toSet

  private def isObjectLike(k: GlobalKind): Boolean = k.isInstanceOf[GlobalKind.Object] || k.isInstanceOf[GlobalKind.Family]

  /** Whether `g` is declared by the bundled standard library (the prelude or a `std/` module). */
  private def fromPrelude(g: GlobalEntry): Boolean = g.declSpan.exists && hugin.compiler.StdlibCache.isStdlib(g.declSpan.source.path)

  /** The object-level name of an object constant: a prelude constant that the program redeclares is
   *  qualified with `prelude` (`prelude.pair`), also in the names of its instances. */
  def objectName(id: Int): Name =
    val g = globals(id)
    g.instanceOf match
      case Some((fam, _)) => objectName(fam) + g.name.drop(globals(fam).name.length)
      case None => if fromPrelude(g) && ownNames(g.name) then s"prelude.${g.name}" else g.name

  private def relKind(d: ObjDecl): RelKind = d match
    case ObjDecl.Constructor => RelKind.Ctor
    case ObjDecl.Struct => RelKind.Struct
    case _ => RelKind.Plain

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
