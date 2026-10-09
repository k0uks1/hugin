package hugin.core

import hugin.util.Span

/** Why unification failed. */
enum UnifyFailure:
  case Mismatch
  case Occurs(m: Int)
  case Escape(lvl: Int)
  case Universe
  case NonPattern

  /** The unknown `m` belongs to an earlier top-level block: it is frozen ([[Core.isFrozen]]). */
  case Frozen(m: Int)

  /** A meta would have to be solved while comparing without unfolding ([[ConvState.Flex]]). */
  case FlexSolution

  /** A record lacks a field of the expected record type (a module lacks a member of its signature). */
  case MissingField(label: Name)

  /** A field does not coerce to the expected record type's field. */
  case Field(label: Name, found: Val, expected: Val)

/** The state of approximate conversion (smalltt): `Rigid` may solve metas and unfolds definitions as
 *  needed, `Flex` compares without solving or unfolding, `Full` unfolds every definition. */
enum ConvState:
  case Rigid, Flex, Full

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
        case Head.Module(_, _) => None
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

  def unifySp(l: Int, sp: Spine, sp2: Spine, cs: ConvState = ConvState.Rigid): Unit =
    if sp.length != sp2.length then fail()
    sp.zip(sp2).foreach {
      case (Elim.EApp(a, _), Elim.EApp(b, _)) => unify(l, a, b, cs)
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
    if sp.length != sp2.length || !onlyApps(sp) || !onlyApps(sp2) then unifySp(l, sp, sp2, ConvState.Rigid)
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
      if pr.exists(_.isEmpty) then unifySp(l, sp, sp2, ConvState.Rigid)
      else
        val p = pr.map(_.get)
        if p.exists(_.isEmpty) then pruneMeta(p, m)

  /** Unifies `t` and `u`, approximately first (smalltt's conversion states, [[ConvState]]):
   *
   *  - `Rigid` (the start): two applications of the same definition ([[Val.Top]]) are compared by their
   *    arguments in `Flex`; if that fails, both are unfolded and compared in `Full`. Of two different
   *    definitions the later one (the larger id: a definition only refers to earlier ones) is unfolded
   *    first; a definition against anything else is unfolded.
   *  - `Flex`: no meta is solved, no definition unfolded, no level constraint added; a mismatch here only
   *    means that the arguments did not match without unfolding.
   *  - `Full`: definitions are unfolded at once.
   *
   *  In `Rigid` and `Full`, an unknown against a definition is solved with the folded form (`?m := vec2`,
   *  `?m := f` rather than `[x] f x`), and with the unfolded value if that fails.
   *
   *  Applications of functions defined by clauses that are stuck on a neutral are compared by their
   *  arguments in every state, as before. */
  def unify(l: Int, t: Val, u: Val, cs: ConvState = ConvState.Rigid): Unit =
    val t1 = forceMetas(t)
    val u1 = forceMetas(u)
    (t1, u1) match
      case (Flex(m, sp), r: Top) if cs != ConvState.Flex && !isFrozen(m) => solveFolded(l, m, sp, r, t1, u1, cs)
      case (r: Top, Flex(m, sp)) if cs != ConvState.Flex && !isFrozen(m) => solveFolded(l, m, sp, r, t1, u1, cs)
      case _ if cs == ConvState.Full => unifyForced(l, unfoldTop(t1), unfoldTop(u1), cs)
      case (Top(f, sp, uf), Top(g, sp2, ug)) =>
        if f == g then
          if cs == ConvState.Flex then unifySp(l, sp, sp2, ConvState.Flex)
          else
            try unifySp(l, sp, sp2, ConvState.Flex)
            catch case _: UnifyError => unify(l, uf.value, ug.value, ConvState.Full)
        else if cs == ConvState.Flex then fail()
        else if f > g then unify(l, uf.value, u1, cs)
        else unify(l, t1, ug.value, cs)
      case (Top(_, _, _), _) | (_, Top(_, _, _)) if cs == ConvState.Flex => fail()
      case (Top(_, _, uf), _) => unify(l, uf.value, u1, cs)
      case (_, Top(_, _, ug)) => unify(l, t1, ug.value, cs)
      case _ => unifyForced(l, t1, u1, cs)

  /** `?m sp =? r` with `r` a folded definition: solved with the folded form (eta-short: `?m := f`), and if
   *  that fails (the folded form mentions what the solution may not), with the sides unfolded. */
  private def solveFolded(l: Int, m: Int, sp: Spine, r: Val, t1: Val, u1: Val, cs: ConvState): Unit =
    try undoOnFailure(solve(l, m, sp, r))
    catch case _: UnifyError => unifyForced(l, unfoldTop(t1), unfoldTop(u1), cs)

  /** A value from [[forceMetas]] forced completely: `force` unfolds the definition at its head. */
  private def unfoldTop(v: Val): Val = v match
    case Top(_, _, u) => force(u.value)
    case other => other

  private def unifyForced(l: Int, t: Val, u: Val, cs: ConvState): Unit = (t, u) match
    case (U0, U0) =>
    // in `Flex`, a level equation only holds if it is already known; no constraint is added
    case (U1(a), U1(b)) =>
      val ok = if cs == ConvState.Flex then a == b else levels.eq(a, b)
      if !ok then fail(UnifyFailure.Universe)
    case (Pi(_, i, a, b), Pi(_, i2, a2, b2)) if i == i2 =>
      unify(l, a, a2, cs)
      unify(l + 1, inst(b, Val.local(l)), inst(b2, Val.local(l)), cs)
    case (Lift(a), Lift(b)) => unify(l, a, b, cs)
    case (Quote(a), Quote(b)) => unify(l, a, b, cs)
    case (Rigid(h, sp), Rigid(h2, sp2)) if h == h2 => unifySp(l, sp, sp2, cs)
    case (Rigid(Head.Glob(i), sp), Rigid(Head.Glob(f), sp2)) if isInstanceOf(i, f) => unifyInstance(l, i, sp, sp2, cs)
    case (Rigid(Head.Glob(f), sp), Rigid(Head.Glob(i), sp2)) if isInstanceOf(i, f) => unifyInstance(l, i, sp2, sp, cs)
    case (RecTy(ls, e, ts, _, _), RecTy(ls2, e2, ts2, _, _)) if ls == ls2 =>
      var env1 = e
      var env2 = e2
      var lv = l
      ts.zip(ts2).foreach { (a, b) =>
        unify(lv, eval(env1, a), eval(env2, b), cs)
        env1 = Val.local(lv) :: env1
        env2 = Val.local(lv) :: env2
        lv += 1
      }
    case (Rec(fs), Rec(fs2)) if fs.map(_._1) == fs2.map(_._1) =>
      fs.zip(fs2).foreach((a, b) => unify(l, a._2, b._2, cs))
    case (Lit(a, s), Lit(b, s2)) if a == b && s == s2 =>
    case (Base(a, s), Base(b, s2)) if a == b && s == s2 =>
    case (RelT, RelT) | (PropT, PropT) =>
    case (Arith(op, a, b, s), Arith(op2, a2, b2, s2)) if op == op2 && s == s2 =>
      unify(l, a, a2, cs); unify(l, b, b2, cs)
    case (Negate(a, s), Negate(b, s2)) if s == s2 => unify(l, a, b, cs)
    case (Obj(ObjForm.Loc(_), List(a)), u1) => unify(l, a, u1, cs)
    case (t1, Obj(ObjForm.Loc(_), List(b))) => unify(l, t1, b, cs)
    case (Obj(f, as), Obj(f2, bs)) if f == f2 && as.length == bs.length => as.zip(bs).foreach((a, b) => unify(l, a, b, cs))
    case (Persist(a), Persist(b)) => unify(l, a, b, cs)
    case (FactTy(a), FactTy(b)) => unify(l, a, b, cs)
    case (Lam(_, _, c), Lam(_, _, c2)) => unify(l + 1, inst(c, Val.local(l)), inst(c2, Val.local(l)), cs)
    case (t1, Lam(_, i, c2)) => unify(l + 1, app(t1, Val.local(l), i), inst(c2, Val.local(l)), cs)
    case (Lam(_, i, c), u1) => unify(l + 1, inst(c, Val.local(l)), app(u1, Val.local(l), i), cs)
    // no meta is solved in `Flex`
    case (Flex(m, sp), Flex(m2, sp2)) if cs == ConvState.Flex =>
      if m == m2 then unifySp(l, sp, sp2, cs) else fail(UnifyFailure.FlexSolution)
    case (Flex(_, _), _) | (_, Flex(_, _)) if cs == ConvState.Flex => fail(UnifyFailure.FlexSolution)
    case (Flex(m, sp), Flex(m2, sp2)) =>
      if m == m2 then if isFrozen(m) then unifySp(l, sp, sp2, cs) else intersect(l, m, sp, sp2)
      else if isFrozen(m) && isFrozen(m2) then fail(UnifyFailure.Frozen(m))
      else if isFrozen(m) then solve(l, m2, sp2, Flex(m, sp))
      else if isFrozen(m2) then solve(l, m, sp, Flex(m2, sp2))
      else flexFlex(l, m, sp, m2, sp2)
    case (Flex(m, sp), u1) => if isFrozen(m) then fail(UnifyFailure.Frozen(m)) else solve(l, m, sp, u1)
    case (t1, Flex(m, sp)) => if isFrozen(m) then fail(UnifyFailure.Frozen(m)) else solve(l, m, sp, t1)
    // η for code: ⟨t⟩ = u iff t = $u
    case (Quote(a), u1 @ Rigid(_, _)) => unify(l, a, vSplice(u1), cs)
    case (t1 @ Rigid(_, _), Quote(b)) => unify(l, vSplice(t1), b, cs)
    case (Rec(fs), u1) => fs.foreach((lb, v) => unify(l, v, proj(u1, lb), cs))
    case (t1, Rec(fs)) => fs.foreach((lb, v) => unify(l, proj(t1, lb), v, cs))
    case _ => fail()

  /** Conversion checking of values without metavariables (definitional equality). */
  def conv(l: Int, t: Val, u: Val): Boolean =
    try
      unify(l, t, u)
      true
    catch case _: UnifyError => false

  def metaSpan(m: Int): Span = metas(m).span
