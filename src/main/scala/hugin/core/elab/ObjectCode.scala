package hugin.core
package elab

import hugin.syntax.Tree
import hugin.syntax.Trees.*
import hugin.util.*

/** The forms of object code that have no meta-level counterpart (REDESIGN §3.1): `as`, ascriptions,
 *  projections and updates of facts, aggregates, unions, wildcards; and positions.
 *
 *  **Object typing is deferred.** The core types object code by unification only, which is enough to
 *  stage it and to solve implicit arguments; the object level's own typing (subtyping, unions,
 *  refinements, fact types of relations, labels of projections) is the object typer's
 *  (`obj/typing/ObjTyper`, REDESIGN §3.4), which sees the staged program. So the core never rejects
 *  object code for its object types: where two object types do not unify, the term is kept as it is
 *  ([[Coercions.coe]]), and the forms below get the types they would have without subtyping, or unknown
 *  ones. Only the *shape* of object code is the core's business: stages, arities, labels of named
 *  patterns.
 *
 *  **Positions.** An object term or formula elaborated from a tree is wrapped in the tree's position
 *  ([[located]]); evaluation keeps positions, so the staged program has them for its diagnostics. */
trait ObjectCode:
  self: Elaborator =>
  import core.*

  /** `tm`, elaborated from a tree at `span`, at its position if it is an object term or formula (object
   *  types carry no positions). The innermost position wins (`(X)` has the position of `X`). */
  def located(span: Span, tm: Tm, ty: Val, st: Stage): Tm =
    if st != Stage.S0 || isUniverse(ty) then tm
    else
      tm match
        case Tm.Obj(ObjForm.Loc(_), _) => tm
        case _ => Tm.loc(span, tm)

  /** An unknown object type (for object terms whose type the core does not determine). */
  def unknownObjectType(c: Cxt, span: Span, what: String): Val =
    ev(c, freshMeta(c, Val.U0, Stage.S0, span, what, allowUnsolved = true))

  /** Infers the object-only forms; `None` for other trees. */
  def inferObjectForm(c: Cxt, t: Tree): Option[(Tm, Val, Stage)] = t match
    case As(x, v) =>
      val (xt, xty) = inferS(c, x, Stage.S0)
      val (vt, _) = inferS(c, v, Stage.S0)
      Some((Tm.Obj(ObjForm.As, List(xt, vt)), xty, Stage.S0))
    case With(v, fields) =>
      dupLabels(fields.map(_.label))
      val (vt, vty) = inferS(c, v, Stage.S0)
      val es = fields.map(f => inferS(c, f.value, Stage.S0)._1)
      Some((Tm.Obj(ObjForm.With(fields.map(f => (f.label.name, f.label.span))), vt :: es), vty, Stage.S0))
    case Union(_, _) => Some((checkUnion(c, t), Val.U0, Stage.S0))
    case BoundType(k, _) => fail(ObjectProblem.BoundOutsideRelation(k.show, t.span))
    case _: Agg => fail(ObjectProblem.UnboundAggregate(t.span))
    case _ => None

  /** `A₁ | … | Aₙ`: an object union type. */
  def checkUnion(c: Cxt, t: Tree): Tm =
    def members(t: Tree): List[Tree] = t match
      case Union(l, r) => members(l) ++ members(r)
      case Parens(i @ Union(_, _)) => members(i)
      case other => List(other)
    Tm.Obj(ObjForm.Union, members(t).map(check(c, _, Val.U0, Stage.S0)))

  /** `(e : A)` with an object type `A`: an object ascription (checked by the object typer). */
  def objectAscription(c: Cxt, e: Tree, at: Tm): (Tm, Val, Stage) =
    val av = ev(c, at)
    (Tm.Obj(ObjForm.Ascribe, List(check(c, e, av, Stage.S0), at)), av, Stage.S0)

  /** `q.l` on object code: a projection of a fact by column label. Its type is the column's if the fact
   *  type of `q` is known to have it, otherwise unknown (the object typer resolves projections on unions
   *  and reports unknown labels). */
  def objectProjection(c: Cxt, sel: Select, qt: Tm, qty: Val): (Tm, Val, Stage) =
    val known = force(qty) match
      case Val.FactTy(r) => columns(r).find(_._1 == sel.name).map(_._2)
      case _ => None
    val ty = known.getOrElse(unknownObjectType(c, sel.span, s"the type of `.${sel.name}`"))
    (Tm.Obj(ObjForm.Proj(sel.name), List(qt)), ty, Stage.S0)

  /** `X = k { t | φ }`: an aggregate over the formula `φ`, its result bound to `X`. */
  def inferAggregate(c: Cxt, res: Tree, agg: Agg): (Tm, Val, Stage) =
    val (rt, _) = inferS(c, res, Stage.S0)
    val (tt, _) = inferS(c, agg.term, Stage.S0)
    val body = check(c, agg.body, Val.PropT, Stage.S0)
    (Tm.Obj(ObjForm.Agg(agg.kind), List(rt, tt, body)), Val.PropT, Stage.S0)

  /** Whether a type is the type of object data (values of object terms), as opposed to formulas, types
   *  and functions. Coercions between such types are left to the object typer. */
  def isObjectData(v: Val): Boolean = force(v) match
    case Val.PropT | Val.U0 | Val.U1(_) | Val.Lift(_) | Val.Pi(_, _, _, _) | Val.RecTy(_, _, _) => false
    case Val.RelT | Val.Flex(_, _) => true
    case other => stageOfType(other) == Stage.S0

  def isAggregate(t: Tree): Boolean = t match
    case _: Agg => true
    case Parens(i) => isAggregate(i)
    case _ => false
