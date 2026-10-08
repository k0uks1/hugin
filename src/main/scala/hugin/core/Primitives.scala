package hugin.core

import hugin.syntax.Literal
import hugin.util.Span
import scala.collection.mutable

/** The primitive operations of the prelude on reflective data (REDESIGN §7.4, C3): what a directive needs
 *  to know about object constants that their data does not say (reflection is untyped, Q5).
 *
 *  - `eqsym : sym -> sym -> bool`: whether two symbols are the same object constant (the first
 *    constructor of `bool` if so, the second otherwise);
 *  - `labels : sym -> seq string`: the labels of a constant's columns (`""` for a column without one), the
 *    index of the typed modes of `%demand` (`modes (labels r)`);
 *  - `derive : sym -> string -> sym`: the object constant `r.l` *derived* from `r` (`typed.check`),
 *    created once per constant and label, so its name is stable and cannot capture a name of the program.
 *    It is *pending* until data declares it (an item `irelation (derive r "check") cols`); a reference to
 *    an undeclared derived constant is a reflection error;
 *  - `derived : sym -> bool`: whether a symbol is a derived constant.
 *
 *  They reduce on closed arguments only (a symbol is closed when it is a quoted object constant); on
 *  anything else they are stuck, like a function on a neutral. */
enum PrimOp(val key: String):
  case EqSym extends PrimOp("eqsym")
  case Labels extends PrimOp("labels")
  case Derive extends PrimOp("derive")
  case Derived extends PrimOp("derived")

  def arity: Int = this match
    case Labels | Derived => 1
    case EqSym | Derive => 2

object PrimOp:
  def byKey(k: String): Option[PrimOp] = values.find(_.key == k)

trait Primitives:
  self: Core =>
  import Val.*

  private val derived = mutable.LinkedHashMap.empty[(Int, String), Int]

  protected def copyPrimitives(from: Primitives): Unit = derived ++= from.derived

  /** The global a derived constant was derived from, and its label. */
  def derivedFrom(id: Int): Option[(Int, String)] = derived.collectFirst { case (k, `id`) => k }

  /** The application of primitive `op` (building `ctors`) to `args`, if they are canonical. */
  def reducePrimitive(op: PrimOp, ctors: List[Int], args: List[Val]): Option[Val] =
    (op, args.map(forceData)) match
      case (PrimOp.EqSym, List(a, b)) =>
        for x <- symbolId(a); y <- symbolId(b) yield Rigid(Head.Glob(if x == y then ctors(0) else ctors(1)), Nil)
      case (PrimOp.Derived, List(a)) =>
        symbolId(a).map(id => Rigid(Head.Glob(if derivedFrom(id).isDefined then ctors(0) else ctors(1)), Nil))
      case (PrimOp.Labels, List(a)) =>
        symbolId(a).map(id => stringList(columnLabels(id), ctors))
      case (PrimOp.Derive, List(a, Lit(Literal.StrL(l), Stage.S1))) =>
        symbolId(a).map(id => Quote(Rigid(Head.Glob(derive(id, l)), Nil)))
      case _ => None

  private def symbolId(v: Val): Option[Int] = v match
    case Quote(t) =>
      forceData(t) match
        case Rigid(Head.Glob(id), Nil) => Some(id)
        case _ => None
    case _ => None

  /** The labels of the explicit object columns of a constant (or family: after its type parameters). */
  def columnLabels(id: Int): List[String] = objectColumns(globals(id).ty).map((x, _) => if x == "_" then "" else x)

  /** The explicit columns of an object constant's type (a family's after its parameters, instantiated with
   *  `_`), with their names and types. */
  def objectColumns(ty: Val): List[(Name, Val)] = force(ty) match
    case Pi(_, Icit.Impl, _, cl) => objectColumns(inst(cl, Val.Wild))
    case Pi(x, Icit.Expl, d, cl) if isObjectType(d) => (x, d) :: objectColumns(inst(cl, Val.Wild))
    case Pi(_, Icit.Expl, _, cl) => objectColumns(inst(cl, Val.Wild))
    case Lift(t) => objectColumns(t)
    case _ => Nil

  private def isObjectType(d: Val): Boolean = force(d) match
    case Lift(_) => false
    case U0 | U1(_) => false
    case Base(_, Stage.S1) => false
    case _ => true

  private def stringList(xs: List[String], ctors: List[Int]): Val =
    val (snil, scons) = (ctors(0), ctors(1))
    val str = Base(hugin.obj.BaseType.StringT, Stage.S1)
    xs.foldRight(Rigid(Head.Glob(snil), List(Elim.EApp(str, Icit.Impl))): Val) { (x, acc) =>
      Rigid(Head.Glob(scons), List(Elim.EApp(acc, Icit.Expl), Elim.EApp(Lit(Literal.StrL(x), Stage.S1), Icit.Expl), Elim.EApp(str, Icit.Impl)))
    }

  /** The derived constant `r.l`, created (pending) on first use. */
  private def derive(id: Int, label: String): Int =
    derived.getOrElseUpdate(
      (id, label), {
        val g = globals(id)
        addGlobal(GlobalEntry(
          s"${g.name}.$label",
          RelT,
          Tm.RelT,
          Stage.S0,
          GlobalKind.Object(ObjDecl.Relation),
          g.span,
          g.declSpan,
          pending = true
        ))
      }
    )

  /** Declares the derived constant `id` as a relation of type `ty` (closed), placed at `at`; false if it
   *  is not a pending derived constant. */
  def declareDerived(id: Int, ty: Tm, at: Span): Boolean =
    val g = globals(id)
    if !g.pending || derivedFrom(id).isEmpty then false
    else
      globals(id) = GlobalEntry(g.name, eval(Nil, ty), ty, g.stage, g.kind, g.span, g.declSpan, placedAt = at)
      true
