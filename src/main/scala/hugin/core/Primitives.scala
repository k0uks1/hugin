package hugin.core

import hugin.syntax.Literal
import hugin.util.Span
import scala.collection.mutable

/** The primitive operations of the prelude on reflective data (reference: directives, C3): what a directive needs
 *  to know about object constants that their data does not say (reflection is untyped, Q5).
 *
 *  - `same : A -> A -> bool`: whether two atoms (meta literals, symbols: the values with decidable
 *    equality that clauses split on) are equal (the first constructor of `bool` if so, the second
 *    otherwise); stuck on other values;
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
  case Same extends PrimOp("same")
  case Labels extends PrimOp("labels")
  case Derive extends PrimOp("derive")
  case Derived extends PrimOp("derived")

  /** The arguments, implicit ones included. */
  def arity: Int = this match
    case Labels | Derived => 1
    case Derive => 2
    case Same => 3

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
      case (PrimOp.Same, List(a, b)) =>
        for x <- atomKey(a); y <- atomKey(b)
        yield Rigid(Head.Glob(if stripPositions(x) == stripPositions(y) then ctors(0) else ctors(1)), Nil)
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
      Rigid(
        Head.Glob(scons),
        List(Elim.EApp(acc, Icit.Expl), Elim.EApp(Lit(Literal.StrL(x), Stage.S1), Icit.Expl), Elim.EApp(str, Icit.Impl))
      )
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

  /** Declares the derived constant `id` as the relation over the columns `cols` (an object constant and
   *  the index of one of its columns each), placed at `at`; the reason if it cannot. A column of a family
   *  makes the derived relation a family with the same parameters (`len.check` of `len : list A -> int
   *  -> rel` is `{A} -> list A -> rel`); its columns must then all be the family's. */
  def declareDerived(id: Int, cols: List[(Int, Int)], at: Span): Option[String] =
    val g = globals(id)
    if !g.pending || derivedFrom(id).isEmpty then
      Some(if derivedFrom(id).isEmpty then s"`${g.name}` is not a derived constant (`derive`)" else s"`${g.name}` is declared twice")
    else
      val families = cols.map(_._1).distinct.filter(o => globals(o).kind.isInstanceOf[GlobalKind.Family])
      families match
        case Nil =>
          val doms = cols.map((o, k) => objectColumns(globals(o).ty).lift(k))
          if doms.exists(_.isEmpty) then Some("a column index out of range")
          else
            val ty = doms.flatten.foldRight(Tm.RelT: Tm)((col, acc) => Tm.Pi(col._1, Icit.Expl, quote(0, col._2), acc))
            globals(id) = GlobalEntry(g.name, eval(Nil, ty), ty, Stage.S0, g.kind, g.span, g.declSpan, placedAt = at)
            None
        case List(fam) if cols.forall(_._1 == fam) =>
          val n = globals(fam).kind match
            case GlobalKind.Family(_, n) => n
            case _ => 0
          // the family's parameters, at levels 0 … n-1, and the selected columns under them
          var t = force(globals(fam).ty)
          val params = (0 until n).toList.map { l =>
            t match
              case Pi(x, i, d, cl) =>
                t = force(inst(cl, Val.local(l)))
                (x, i, quote(l, d))
              case other => throw Impossible(s"family type $other")
          }
          val columns = objectColumns(t)
          if cols.exists((_, k) => k >= columns.length) then Some("a column index out of range")
          else
            val selected = cols.map((_, k) => columns(k)).zipWithIndex.map { case ((x, d), j) => (x, quote(n + j, d)) }
            val objTy = selected.foldRight(Tm.RelT: Tm)((col, acc) => Tm.Pi(col._1, Icit.Expl, col._2, acc))
            val ty = params.foldRight(Tm.Lift(objTy): Tm)((p, acc) => Tm.Pi(p._1, p._2, p._3, acc))
            val kind = GlobalKind.Family(ObjDecl.Relation, n)
            globals(id) = GlobalEntry(g.name, eval(Nil, ty), ty, Stage.S1, kind, g.span, g.declSpan, placedAt = at)
            None
        case _ => Some("columns of a family and of other constants")
