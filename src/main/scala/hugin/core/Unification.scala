package hugin.core

import hugin.util.Span

/** Why unification failed. */
enum UnifyFailure:
  case Mismatch
  case Occurs(m: Int)
  case Escape(lvl: Int)
  case Universe
  case NonPattern

final class UnifyError(val failure: UnifyFailure) extends Exception(failure.toString, null, false, false)

/** Higher-order pattern unification with pruning and the occurs check, after elaboration-zoo
 *  (`05-pruning`) and Kovács's staged elaborator: metas applied to distinct bound variables (also under
 *  quotes and splices) are solved by inverting the spine; arguments outside the pattern fragment are
 *  pruned from metas on the right-hand side where possible; metas whose spines contain splices or
 *  projections are first eta-expanded along their types (`⇑A` by a quote, records by their fields).
 *  Records have eta (a record value equals a neutral if all fields do), as do functions. Universe levels
 *  are unified by adding constraints to [[Levels]]; a meta whose type is a universe gets the constraint
 *  that its solution lives in it. */
trait Unification:
  self: Core =>
  import Val.*

  private def fail(f: UnifyFailure = UnifyFailure.Mismatch): Nothing = throw UnifyError(f)

  /** Solves `?m sp =? rhs` in a context of size `gamma`. */
  def solve(gamma: Int, m: Int, sp: Spine, rhs: Val): Unit =
    val (m2, sp2) = expandFlex(m, sp)
    val inv = invert(gamma, sp2)
    solveWithPSub(m2, inv._1, inv._2, rhs)

  def solveWithPSub(m: Int, psub: PSub, pruneNonlinear: Option[Pruning], rhs: Val): Unit =
    val mty = metas(m).ty
    pruneNonlinear.foreach(pr => pruneTy(pr, mty))
    val rhsTm = psubst(psub.copy(occ = Some(m)), rhs)
    val sol = eval(Nil, lams(psub.dom, mty, rhsTm))
    checkSolutionLevel(mty, psub.dom, sol)
    solveMeta(m, sol)

  /** If the meta's type is a universe `Type l`, its solution must be a type in `Type l`. */
  private def checkSolutionLevel(mty: Val, arity: Int, sol: Val): Unit =
    var ty = mty
    var types = Vector.empty[Val]
    var v = sol
    var k = 0
    var ok = true
    while ok && k < arity do
      force(ty) match
        case Pi(_, i, d, cl) =>
          types :+= d
          ty = inst(cl, Val.local(k))
          v = app(v, Val.local(k), i)
        case _ => ok = false
      k += 1
    if ok then
      force(ty) match
        case U1(l) =>
          for b <- typeLevels(types, arity, v) do if !levels.le(b, l) then fail(UnifyFailure.Universe)
        case _ =>

  /** Lower bounds of the universe level of a type value: it lives in `Type l` for every `l` above all of
   *  them. `types` are the types of the bound variables, by level. */
  def typeLevels(types: Vector[Val], l: Int, v: Val): List[Level] = force(v) match
    case U1(k) => List(k.succ)
    case Pi(_, _, a, cl) => typeLevels(types, l, a) ++ typeLevels(types :+ a, l + 1, inst(cl, Val.local(l)))
    case rt: RecTy =>
      var ts = types
      var lv = l
      var e = rt.env
      rt.tys.flatMap { ty =>
        val tv = eval(e, ty)
        val r = typeLevels(ts, lv, tv)
        ts :+= tv
        e = Val.local(lv) :: e
        lv += 1
        r
      }
    case Rigid(h, sp) =>
      val hty = h match
        case Head.Local(x) => types.lift(x)
        case Head.Glob(id) => Some(globals(id).ty)
      hty.flatMap(t => spineType(t, Rigid(h, Nil), sp)).map(force) match
        case Some(U1(k)) => List(k)
        case _ => Nil
    case Flex(m, sp) =>
      spineType(metas(m).ty, Flex(m, Nil), sp).map(force) match
        case Some(U1(k)) => List(k)
        case _ => Nil
    case _ => Nil

  /** The type of `head sp`, given the type of the head. */
  def spineType(headTy: Val, head: Val, sp: Spine): Option[Val] =
    var ty = headTy
    var cur = head
    var ok = true
    for e <- sp.reverse if ok do
      (e, force(ty)) match
        case (Elim.EApp(a, _), Pi(_, _, _, cl)) =>
          ty = inst(cl, a)
          cur = elim(cur, e)
        case (Elim.ESplice, Lift(a)) =>
          ty = a
          cur = elim(cur, e)
        case (Elim.EProj(lb), rt: RecTy) =>
          fieldType(rt, cur, lb) match
            case Some(t) =>
              ty = t
              cur = elim(cur, e)
            case None => ok = false
        case _ => ok = false
    Option.when(ok)(ty)

  def unifySp(l: Int, sp: Spine, sp2: Spine): Unit =
    if sp.length != sp2.length then fail()
    sp.zip(sp2).foreach {
      case (Elim.EApp(a, _), Elim.EApp(b, _)) => unify(l, a, b)
      case (Elim.ESplice, Elim.ESplice) =>
      case (Elim.EProj(a), Elim.EProj(b)) if a == b =>
      case _ => fail()
    }

  private def flexFlex(gamma: Int, m: Int, sp: Spine, m2: Int, sp2: Spine): Unit =
    val attempt =
      try
        val (m1, sp1) = expandFlex(m, sp)
        Some((m1, invert(gamma, sp1)))
      catch case _: UnifyError => None
    attempt match
      case None => solve(gamma, m2, sp2, Flex(m, sp))
      case Some((m1, inv)) => solveWithPSub(m1, inv._1, inv._2, Flex(m2, sp2))

  /** `?m sp =? ?m sp2`: prune the arguments on which the spines differ. */
  private def intersect(l: Int, m: Int, sp: Spine, sp2: Spine): Unit =
    if sp.length != sp2.length || !onlyApps(sp) || !onlyApps(sp2) then unifySp(l, sp, sp2)
    else
      def varOf(v: Val): Option[Int] = force(v) match
        case Rigid(Head.Local(x), Nil) => Some(x)
        case _ => None
      val pr = sp.zip(sp2).map {
        case (Elim.EApp(a, i), Elim.EApp(b, _)) =>
          (varOf(a), varOf(b)) match
            case (Some(x), Some(y)) => Some(if x == y then Some(i) else None)
            case _ => None
        case _ => None
      }
      if pr.exists(_.isEmpty) then unifySp(l, sp, sp2)
      else
        val p = pr.map(_.get)
        if p.exists(_.isEmpty) then pruneMeta(p, m)

  def unify(l: Int, t: Val, u: Val): Unit = (force(t), force(u)) match
    case (U0, U0) =>
    case (U1(a), U1(b)) => if !levels.eq(a, b) then fail(UnifyFailure.Universe)
    case (Pi(_, i, a, b), Pi(_, i2, a2, b2)) if i == i2 =>
      unify(l, a, a2)
      unify(l + 1, inst(b, Val.local(l)), inst(b2, Val.local(l)))
    case (Lift(a), Lift(b)) => unify(l, a, b)
    case (Quote(a), Quote(b)) => unify(l, a, b)
    case (Rigid(h, sp), Rigid(h2, sp2)) if h == h2 => unifySp(l, sp, sp2)
    case (RecTy(ls, e, ts), RecTy(ls2, e2, ts2)) if ls == ls2 =>
      var env1 = e
      var env2 = e2
      var lv = l
      ts.zip(ts2).foreach { (a, b) =>
        unify(lv, eval(env1, a), eval(env2, b))
        env1 = Val.local(lv) :: env1
        env2 = Val.local(lv) :: env2
        lv += 1
      }
    case (Rec(fs), Rec(fs2)) if fs.map(_._1) == fs2.map(_._1) =>
      fs.zip(fs2).foreach((a, b) => unify(l, a._2, b._2))
    case (Lit(a, s), Lit(b, s2)) if a == b && s == s2 =>
    case (Base(a, s), Base(b, s2)) if a == b && s == s2 =>
    case (RelT, RelT) | (PropT, PropT) =>
    case (Arith(op, a, b, s), Arith(op2, a2, b2, s2)) if op == op2 && s == s2 =>
      unify(l, a, a2); unify(l, b, b2)
    case (Negate(a, s), Negate(b, s2)) if s == s2 => unify(l, a, b)
    case (Obj(ObjForm.Loc(_), List(a)), u1) => unify(l, a, u1)
    case (t1, Obj(ObjForm.Loc(_), List(b))) => unify(l, t1, b)
    case (Obj(f, as), Obj(f2, bs)) if f == f2 && as.length == bs.length => as.zip(bs).foreach((a, b) => unify(l, a, b))
    case (Persist(a), Persist(b)) => unify(l, a, b)
    case (FactTy(a), FactTy(b)) => unify(l, a, b)
    case (Lam(_, _, c), Lam(_, _, c2)) => unify(l + 1, inst(c, Val.local(l)), inst(c2, Val.local(l)))
    case (t1, Lam(_, i, c2)) => unify(l + 1, app(t1, Val.local(l), i), inst(c2, Val.local(l)))
    case (Lam(_, i, c), u1) => unify(l + 1, inst(c, Val.local(l)), app(u1, Val.local(l), i))
    case (Flex(m, sp), Flex(m2, sp2)) =>
      if m == m2 then intersect(l, m, sp, sp2) else flexFlex(l, m, sp, m2, sp2)
    case (Flex(m, sp), u1) => solve(l, m, sp, u1)
    case (t1, Flex(m, sp)) => solve(l, m, sp, t1)
    case (Rec(fs), u1) => fs.foreach((lb, v) => unify(l, v, proj(u1, lb)))
    case (t1, Rec(fs)) => fs.foreach((lb, v) => unify(l, proj(t1, lb), v))
    case _ => fail()

  /** Conversion checking of values without metavariables (definitional equality). */
  def conv(l: Int, t: Val, u: Val): Boolean =
    try
      unify(l, t, u)
      true
    catch case _: UnifyError => false

  def metaSpan(m: Int): Span = metas(m).span
