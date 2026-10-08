package hugin.core
package elab

import hugin.syntax.Tree
import hugin.util.*

/** Stage inference and subtyping by coercion (Kovács, ICFP 2022, §4): `coe` inserts quotes, splices,
 *  lifts, persistence of primitives and record coercions, and falls back to unification. */
trait Coercions:
  self: Elaborator =>
  import core.*

  /** Coerces `t : a` (stage `s`) to `a2` (stage `s2`), inserting quotes, splices, lifts and record
   *  coercions; falls back to unification. */
  def coe(c: Cxt, span: Span, t: Tm, a: Val, s: Stage, a2: Val, s2: Stage): Tm =
    try
      if s2 == Stage.S0 && isObjectData(a2) then
        // object data is coerced softly (the object typer decides), also a persisted meta primitive
        val moved = if s == Stage.S1 && isMetaPrim(a).isDefined then adjustStage(c, t, a, s, s2) else None
        moved match
          case Some((t1, a1)) => coeObjectData(c, t1, a1, a2)
          case None if s == Stage.S0 && isObjectData(a) => coeObjectData(c, t, a, a2)
          case None => coeOpt(c, t, a, s, a2, s2).getOrElse(t)
      else coeOpt(c, t, a, s, a2, s2).getOrElse(t)
    catch
      case e: UnifyError =>
        expectedRelation(a2).foreach { r =>
          dataConstructorOf(t).foreach(dataUsedAsRelation(_, span, s"expected a relation `⇑(${show(c, r)})`"))
        }
        fail(mismatch(c, span, a2, s2, a, s, e.failure))

  private def expectedRelation(a: Val): Option[Val] = force(a) match
    case Val.Lift(x) => Option.when(isRelationType(x))(x)
    case other => Option.when(isRelationType(other))(other)

  /** Object data between object types: unified if possible (which solves implicit arguments and the
   *  types of variables); otherwise left to the object typer, which knows subtyping ([[ObjectCode]]). */
  private def coeObjectData(c: Cxt, t: Tm, a: Val, a2: Val): Tm =
    try undoOnFailure(unify(c.lvl, dataType(c, t, a), a2))
    catch case _: UnifyError => ()
    t

  /** The type of object data `t : a`; a fact term of a relation or struct (`pair 1 "x"`, of type `rel`) is
   *  of the relation's fact type. */
  private def dataType(c: Cxt, t: Tm, a: Val): Val = force(a) match
    case Val.RelT =>
      def head(t: Tm): Tm = Tm.unloc(t) match
        case Tm.App(f, _, Icit.Expl) => head(f)
        case other => other
      Val.FactTy(ev(c, head(t)))
    case other => other

  private def adjustStage(c: Cxt, t: Tm, a: Val, s: Stage, s2: Stage): Option[(Tm, Val)] =
    (s, s2) match
      case (Stage.S0, Stage.S1) => Some((Tm.quote(t), Val.Lift(a)))
      case (Stage.S1, Stage.S0) =>
        force(a) match
          case Val.Lift(x) => Some((Tm.splice(t), x))
          case Val.Base(b, Stage.S1) => Some((Tm.Persist(t), Val.Base(b, Stage.S0)))
          case other =>
            val m = ev(c, freshMeta(c, Val.U0, Stage.S0, Span.NoSpan, "object type"))
            unify(c.lvl, other, Val.Lift(m))
            Some((Tm.splice(t), m))
      case _ => None

  private def justUnify(c: Cxt, t: Tm, a: Val, s: Stage, a2: Val, s2: Stage): Option[Tm] =
    adjustStage(c, t, a, s, s2) match
      case None =>
        unify(c.lvl, a, a2)
        None
      case Some((t1, a1)) =>
        unify(c.lvl, a1, a2)
        Some(t1)

  /** A type `t : type` used where a meta type is expected: `⇑t`, or the meta primitive for a base type. */
  def liftType(c: Cxt, t: Tm): Tm = force(ev(c, t)) match
    case Val.Base(b, Stage.S0) => Tm.Base(b, Stage.S1)
    case _ => Tm.Lift(t)

  private def coeOpt(c: Cxt, t: Tm, a: Val, s: Stage, a2: Val, s2: Stage): Option[Tm] =
    (force(a), force(a2)) match
      case (Val.Pi(x, i, d, b), Val.Pi(x2, i2, d2, b2)) =>
        if i != i2 then throw UnifyError(UnifyFailure.Mismatch)
        val c2 = bind(c, x2, d2, s2)
        val tw = Tm.shift(t, 1)
        coeOpt(c2, Tm.Var(0), d2, s2, d, s) match
          case None =>
            coeOpt(c2, Tm.App(tw, Tm.Var(0), i), inst(b, Val.local(c.lvl)), s, inst(b2, Val.local(c.lvl)), s2)
              .map(body => Tm.Lam(x2, i, body))
          case Some(cv) =>
            val body = coeOpt(c2, Tm.App(tw, cv, i), inst(b, ev(c2, cv)), s, inst(b2, Val.local(c.lvl)), s2)
            Some(Tm.Lam(if x2 == "_" then x else x2, i, body.getOrElse(Tm.App(tw, cv, i))))
      case (Val.U0, Val.U1(_)) => Some(liftType(c, t))
      case (rel, Val.U0) if isFactConstantType(rel) => Some(Tm.FactTy(t))
      case (rel, Val.U1(_)) if isFactConstantType(rel) => Some(Tm.Lift(Tm.FactTy(t)))
      case (Val.U1(l), Val.U1(l2)) =>
        if !levels.le(l, l2) then throw UnifyError(UnifyFailure.Universe)
        None
      case (Val.Lift(x), Val.Lift(y)) =>
        unify(c.lvl, x, y)
        None
      case (Val.Flex(_, _), _) | (_, Val.Flex(_, _)) => justUnify(c, t, a, s, a2, s2)
      case (Val.Lift(x), _) => Some(coeOpt(c, Tm.splice(t), x, Stage.S0, a2, s2).getOrElse(Tm.splice(t)))
      case (_, Val.Lift(y)) => Some(Tm.quote(coeOpt(c, t, a, s, y, Stage.S0).getOrElse(t)))
      case (Val.Base(b, Stage.S1), Val.Base(b2, Stage.S0)) if b == b2 => Some(Tm.Persist(t))
      case (Val.RelT, Val.PropT) => None
      case (ty, Val.PropT) if s == Stage.S0 && isConstructorAtom(t, ty) => None
      case (rt: Val.RecTy, rt2: Val.RecTy) => coeRecord(c, t, rt, s, rt2, s2)
      case _ => justUnify(c, t, a, s, a2, s2)

  /** A constructor application of an object type, used as a formula: an atom of the constructor's
   *  relation (in Datalog∃! every constructor is a relation, REDESIGN §3.2). */
  private def isConstructorAtom(t: Tm, ty: Val): Boolean =
    def application(t: Tm): Boolean = Tm.unloc(t) match
      case Tm.App(_, _, _) | Tm.Splice(_) | Tm.Global(_) => true
      case _ => false
    application(t) && stageOfType(ty) == Stage.S0 && !isUniverse(ty)

  /** Record subtyping by coercion: every field of the expected record type must be present (width) and
   *  coerce to the expected field type (depth). */
  private def coeRecord(c: Cxt, t: Tm, rt: Val.RecTy, s: Stage, rt2: Val.RecTy, s2: Stage): Option[Tm] =
    val tv = ev(c, t)
    val fromFields = fieldTypes(rt, l => proj(tv, l)).toMap
    var built = List.empty[(Name, Tm, Val)]
    var changed = rt.labels != rt2.labels
    var e = rt2.env
    for (lb, ty) <- rt2.labels.zip(rt2.tys) do
      val expected = eval(e, ty)
      val found = fromFields.getOrElse(lb, throw UnifyError(UnifyFailure.MissingField(lb)))
      val ft =
        try coeOpt(c, Tm.Proj(t, lb), found, s, expected, s2)
        catch case _: UnifyError => throw UnifyError(UnifyFailure.Field(lb, found, expected))
      if ft.isDefined then changed = true
      val tm = ft.getOrElse(Tm.Proj(t, lb))
      val v = ev(c, tm)
      built = built :+ (lb, tm, v)
      e = v :: e
    Option.when(changed)(Tm.Rec(built.map(b => (b._1, b._2))))

  /** `⇑A`, the explicit lift. */
  def inferLift(c: Cxt, a: Tree): (Tm, Val, Stage) =
    (Tm.Lift(check(c, a, Val.U0, Stage.S0)), Val.U1(Level.zero), Stage.S1)

  /** `$t`, the explicit splice (REDESIGN §6.9): `t` must be meta code of type `⇑A`, or a meta primitive
   *  value (persisted as a literal). */
  def inferSplice(c: Cxt, a: Tree, span: Span): (Tm, Val, Stage) =
    val (at, aty, s) = infer(c, a)
    if s == Stage.S0 then
      fail(TypeProblem.SpliceOfObjectCode(a.span))
    force(aty) match
      case Val.Lift(x) => (Tm.splice(at), x, Stage.S0)
      case Val.Base(b, Stage.S1) => (Tm.Persist(at), Val.Base(b, Stage.S0), Stage.S0)
      case other =>
        val m = ev(c, freshMeta(c, Val.U0, Stage.S0, span, "the object type of a splice"))
        unifyAt(c, a.span, Val.Lift(m), other)
        (Tm.splice(at), m, Stage.S0)

  /** Moves an inferred term to another stage. */
  def adjust(c: Cxt, span: Span, tm: Tm, ty: Val, s: Stage, st: Stage): (Tm, Val) =
    try adjustStage(c, tm, ty, s, st).getOrElse((tm, ty))
    catch
      case e: UnifyError =>
        fail(mismatch(c, span, if st == Stage.S0 then Val.Lift(ty) else ty, st, ty, s, e.failure))
