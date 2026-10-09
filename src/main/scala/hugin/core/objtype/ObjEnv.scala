package hugin.core
package objtype

import scala.collection.mutable

/** The object constants and subtyping edges in scope, and the translation of core values into [[OTy]]:
 *  the globals of `core`, the edges of the program (and of the module instances staged so far), and,
 *  during elaboration, the variables of the context (`locals`). */
final class ObjEnv(val core: Core, locals: ObjEnv.Locals = ObjEnv.NoLocals):
  import core.*

  /** Object types from values (forced; positions and bound columns looked through). */
  def oty(v: Val): OTy = Val.unloc(force(v)) match
    case Val.Base(b, _) => OTy.Base(b)
    case Val.RelT => OTy.RelTop
    case Val.FactTy(r) => head(r).map((h, as) => OTy.Fact(h, as)).getOrElse(OTy.Unknown)
    case Val.Obj(ObjForm.Union, ms) => OTy.union(ms.map(oty))
    case Val.Obj(ObjForm.BoundCol(_), List(t)) => oty(t)
    case other =>
      head(other) match
        case Some((h @ OHead.G(id), as)) if relationGlobal(id) => OTy.Fact(h, as)
        case Some((h, as)) => OTy.Con(h, as)
        case None => OTy.Unknown

  private def relationGlobal(id: Int): Boolean = globals(id).kind match
    case GlobalKind.Object(d) => d != ObjDecl.OpenType && !d.isInstanceOf[ObjDecl.Refinement]
    case _ => false

  /** The head of an object constant or type and its (family) arguments. */
  def head(v: Val): Option[(OHead, List[OTy])] = Val.unloc(force(v)) match
    case Val.Rigid(Head.Glob(id), sp) =>
      val as = args(sp)
      if as.nonEmpty then argVals((OHead.G(id), as)) = sp.reverse.collect { case Elim.EApp(a, _) => a }
      Some((OHead.G(id), as))
    case Val.Rigid(Head.Local(l), sp) =>
      val projs = sp.reverse.collect { case Elim.EProj(x) => x }
      Some((OHead.L(l, projs), Nil))
    case Val.Quote(t) => head(t)
    case Val.Flex(_, _) => None
    case _ => None

  /** The arguments (as values) of the family applications seen, for their columns. */
  private val argVals = mutable.HashMap.empty[(OHead, List[OTy]), List[Val]]

  private def args(sp: Spine): List[OTy] = sp.reverse.collect { case Elim.EApp(a, _) => oty(a) }

  /** The type of an object constant (a closed value for a global, from the context for a variable). */
  def typeOf(h: OHead): Option[Val] = h match
    case OHead.G(id) => Some(globals(id).ty)
    case OHead.L(l, ps) => locals.typeOf(l, ps)

  def name(h: OHead): String = h match
    case OHead.G(id) => globals(id).name
    case OHead.L(l, ps) => (locals.name(l) :: ps).mkString(".")

  /** What a head denotes, at the given family arguments. */
  def kind(h: OHead, as: List[OTy]): HeadKind = h match
    case OHead.G(id) =>
      globals(id).kind match
        case GlobalKind.Object(ObjDecl.OpenType) => HeadKind.Open
        case GlobalKind.Object(ObjDecl.Refinement(b)) => HeadKind.Refinement(oty(eval(Nil, b)))
        case GlobalKind.Object(_) | GlobalKind.Family(_, _) =>
          relInfo(h, as).map(HeadKind.Relation(_)).getOrElse(if isTypeFamily(id) then HeadKind.Open else HeadKind.Abstract)
        case _ => HeadKind.Abstract
    case OHead.L(l, ps) =>
      if locals.isMemberType(l, ps) then HeadKind.Open
      else relInfo(h, as).map(HeadKind.Relation(_)).getOrElse(HeadKind.Abstract)

  private def isTypeFamily(id: Int): Boolean = globals(id).kind match
    case GlobalKind.Family(ObjDecl.OpenType, _) => true
    case _ => false

  private val infos = mutable.HashMap.empty[(OHead, List[OTy]), Option[RelInfo]]

  /** The columns and result of a relation, constructor or struct (`None` for a type). */
  def relInfo(h: OHead, as: List[OTy]): Option[RelInfo] = infos.getOrElseUpdate(
    (h, as), {
      val isFamily = h match
        case OHead.G(id) => globals(id).kind.isInstanceOf[GlobalKind.Family]
        case _ => false
      typeOf(h).flatMap { ty =>
        // a family's type binds its parameters first (`{A : ⇑type} -> ⇑(A -> list A -> list A)`): its
        // columns are seen at unknown parameters
        val objTy = if isFamily then familyBody(ty, argVals.getOrElse((h, as), Nil)) else Some(unlift(ty))
        objTy.flatMap(columns(h, as, _))
      }
    }
  )

  private def unlift(v: Val): Val = force(v) match
    case Val.Lift(t) => t
    case other => other

  private def familyBody(ty: Val, vals: List[Val]): Option[Val] = force(ty) match
    case Val.Pi(_, _, _, cl) => familyBody(inst(cl, vals.headOption.getOrElse(Val.Wild)), vals.drop(1))
    case Val.Lift(t) => Some(t)
    case _ => None

  private def columns(h: OHead, as: List[OTy], ty: Val): Option[RelInfo] =
    def go(t: Val, acc: List[(Option[String], OTy)]): Option[RelInfo] = force(t) match
      case Val.Pi(x, _, d, cl) => go(inst(cl, Val.Wild), (Option.when(x != "_")(x), oty(d)) :: acc)
      case Val.RelT => Some(RelInfo(h, as, name(h), acc.reverse.toVector, None))
      case Val.U0 | Val.PropT => None
      case other if acc.isEmpty && !isConstantResult(other) => None
      case other => Some(RelInfo(h, as, name(h), acc.reverse.toVector, Some(oty(other))))
    go(ty, Nil)

  /** Whether a constant with this type and no columns is a constructor (`nil : list A`, `red : color`). */
  private def isConstantResult(v: Val): Boolean = oty(v) match
    case OTy.Con(_, _) => true
    case _ => false

  /** The relations, constructors and structs in scope (the candidates for the members of a type). */
  def relationHeads: List[RelInfo] =
    val gs = core.relationGlobals.flatMap(id => relInfo(OHead.G(id), Nil))
    gs ++ locals.relationHeads.flatMap(h => relInfo(h, Nil))

  /** The edges `τ <: a` in scope. */
  def edges: List[(OTy, OTy)] =
    core.objEdges.map((sub, sup) => (oty(sub), OTy.Con(OHead.G(sup), Nil))) ++ locals.edges.map((s, t) => (oty(s), oty(t)))

object ObjEnv:
  /** The variables of an elaboration context that are object constants or types. */
  trait Locals:
    def typeOf(lvl: Int, projs: List[String]): Option[Val]
    def name(lvl: Int): String
    def isMemberType(lvl: Int, projs: List[String]): Boolean
    def relationHeads: List[OHead]
    def edges: List[(Val, Val)]

  object NoLocals extends Locals:
    def typeOf(lvl: Int, projs: List[String]): Option[Val] = None
    def name(lvl: Int): String = s"#$lvl"
    def isMemberType(lvl: Int, projs: List[String]): Boolean = false
    def relationHeads: List[OHead] = Nil
    def edges: List[(Val, Val)] = Nil
