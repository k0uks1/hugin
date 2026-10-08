package hugin.core

/** Partial renamings for pattern unification (elaboration-zoo `05-pruning`): inverting a pattern spine,
 *  reading back a right-hand side under the inverse (with the occurs check and scope check), pruning
 *  metas applied to variables outside the renaming, and eta-expanding metas whose spines contain splices
 *  or projections (along `⇑A` by a quote, along record types by their fields). */
trait Renaming:
  self: Core =>
  import Val.*

  private def fail(f: UnifyFailure = UnifyFailure.Mismatch): Nothing = throw UnifyError(f)

  /** A partial substitution from Γ (size `dom`) to Δ (size `cod`): Δ's variables to Γ's values. */
  final case class PSub(occ: Option[Int], dom: Int, cod: Int, sub: Map[Int, Val]):
    def lift: PSub = PSub(occ, dom + 1, cod + 1, sub + (cod -> Val.local(dom)))
    def skip: PSub = PSub(occ, dom, cod + 1, sub)

  /** Inverts a spine of distinct bound variables; a non-linear spine yields the pruning of the repeated
   *  variables (which are then left out of the solution). */
  def invert(gamma: Int, sp: Spine): (PSub, Option[Pruning]) =
    var dom = 0
    var domvars = Set.empty[Int]
    var sub = Map.empty[Int, Val]
    var pr: Pruning = Nil
    var linear = true
    for e <- sp.reverse do
      def invertVal(x: Int, inv: Val, i: Icit): Unit =
        if domvars(x) then
          sub -= x
          pr = None :: pr
          linear = false
        else
          domvars += x
          sub += x -> inv
          pr = Some(i) :: pr
        dom += 1
      e match
        case Elim.EApp(t, i) =>
          force(t) match
            case Rigid(Head.Local(x), Nil) => invertVal(x, Val.local(dom), i)
            case Quote(q) =>
              force(q) match
                case Rigid(Head.Local(x), Nil) => invertVal(x, Rigid(Head.Local(dom), List(Elim.ESplice)), i)
                case _ => fail(UnifyFailure.NonPattern)
            case Rigid(Head.Local(x), List(Elim.ESplice)) => invertVal(x, Quote(Val.local(dom)), i)
            case _ => fail(UnifyFailure.NonPattern)
        case _ => fail(UnifyFailure.NonPattern)
    (PSub(None, dom, gamma, sub), if linear then None else Some(pr))

  /** Removes the arguments not selected by a pruning (innermost first) from a closed Π type. */
  def pruneTy(pr: Pruning, a: Val): Tm =
    def go(prs: List[Option[Icit]], psub: PSub, a: Val): Tm = (prs, force(a)) match
      case (Nil, a) => psubst(psub, a)
      case (Some(_) :: rest, Pi(x, i, d, cl)) =>
        Tm.Pi(x, i, psubst(psub, d), go(rest, psub.lift, inst(cl, Val.local(psub.cod))))
      case (None :: rest, Pi(_, _, _, cl)) => go(rest, psub.skip, inst(cl, Val.local(psub.cod)))
      case _ => throw Impossible("pruning a non-function type")
    go(pr.reverse, PSub(None, 0, 0, Map.empty), a)

  /** Wraps `t` in `l` lambdas named and with icitness after the Π type `a`. */
  def lams(l: Int, a: Val, t: Tm): Tm =
    def go(a: Val, k: Int): Tm =
      if k == l then t
      else
        force(a) match
          case Pi(x, i, _, cl) => Tm.Lam(if x == "_" then s"x$k" else x, i, go(inst(cl, Val.local(k)), k + 1))
          case _ => throw Impossible("lams: not a function type")
    go(a, 0)

  /** Solves `m` by a pruned copy of itself. */
  def pruneMeta(pr: Pruning, m: Int): Val =
    val e = metas(m)
    val prunedTy = eval(Nil, pruneTy(pr, e.ty))
    val m2 = newMeta(prunedTy, e.stage, e.span, e.what, e.allowUnsolved)
    val sol = eval(Nil, lams(pr.length, e.ty, Tm.AppPruning(Tm.Meta(m2), pr)))
    solveMeta(m, sol)
    sol

  /** Eta-expands an unsolved meta along its type, so that splices and projections in its spines reduce:
   *  `⇑A` becomes a quote of a fresh meta, a record type a record of fresh metas. */
  def etaExpandMeta(m: Int): Val =
    val e = metas(m)
    // binders: (name, type term, icit), innermost first
    def go(binders: List[(Name, Tm, Icit)], l: Int, a: Val, st: Stage): Tm = force(a) match
      case Pi(x, i, d, cl) => Tm.Lam(x, i, go((x, quote(l, d), i) :: binders, l + 1, inst(cl, Val.local(l)), st))
      case Lift(b) => Tm.quote(go(binders, l, b, Stage.S0))
      case rt: RecTy =>
        val env = (0 until l).reverse.map(Val.local).toList
        var done = List.empty[(Name, Tm, Val)]
        for (lb, ty) <- rt.labels.zip(rt.tys) do
          val tyV = eval(done.map(_._3).foldLeft(rt.env)((acc, v) => v :: acc), ty)
          val t = fresh(binders, l, tyV, st)
          done = done :+ (lb, t, eval(env, t))
        Tm.Rec(done.map(x => (x._1, x._2)))
      case other => fresh(binders, l, other, st)
    def fresh(binders: List[(Name, Tm, Icit)], l: Int, a: Val, st: Stage): Tm =
      val closed = binders.foldLeft(quote(l, a))((acc, b) => Tm.Pi(b._1, b._3, b._2, acc))
      val m2 = newMeta(eval(Nil, closed), st, e.span, e.what, e.allowUnsolved)
      Tm.AppPruning(Tm.Meta(m2), binders.map(b => Some(b._3)))
    val t = go(Nil, 0, e.ty, e.stage)
    val v = eval(Nil, t)
    solveMeta(m, v)
    v

  def onlyApps(sp: Spine): Boolean = sp.forall(_.isInstanceOf[Elim.EApp])

  /** Eta-expands a meta whose spine contains splices or projections. */
  def expandFlex(m: Int, sp: Spine): (Int, Spine) =
    if onlyApps(sp) then (m, sp)
    else
      val sol = etaExpandMeta(m)
      force(appSp(sol, sp)) match
        case Flex(m2, sp2) => expandFlex(m2, sp2)
        case _ => fail(UnifyFailure.NonPattern)

  /** Prunes the arguments of a flex that the partial substitution does not cover. */
  def pruneFlex(psub: PSub, m: Int, sp: Spine): (Int, Spine) =
    val (m1, sp1) =
      try expandFlex(m, sp)
      catch case _: UnifyError => (m, sp)
    if !onlyApps(sp1) then (m1, sp1)
    else
      val pruning: Option[Pruning] =
        val parts = sp1.map {
          case Elim.EApp(t, i) =>
            val x = force(t) match
              case Rigid(Head.Local(x), Nil) => Some(x)
              case Rigid(Head.Local(x), List(Elim.ESplice)) => Some(x)
              case Quote(q) =>
                force(q) match
                  case Rigid(Head.Local(x), Nil) => Some(x)
                  case _ => None
              case _ => None
            x.map(x => if psub.sub.contains(x) then Some(i) else None)
          case _ => None
        }
        if parts.forall(_.isDefined) then Some(parts.map(_.get)) else None
      pruning match
        case Some(pr) if pr.exists(_.isEmpty) =>
          pruneMeta(pr, m1)
          force(Flex(m1, sp1)) match
            case Flex(m2, sp2) => (m2, sp2)
            case _ => throw Impossible("pruned meta is not flex")
        case _ => (m1, sp1)

  def psubstSp(psub: PSub, h: Tm, sp: Spine): Tm = sp.reverse.foldLeft(h) { (acc, e) =>
    e match
      case Elim.EApp(a, i) => Tm.App(acc, psubst(psub, a), i)
      case Elim.ESplice => Tm.Splice(acc)
      case Elim.EProj(l) => Tm.Proj(acc, l)
  }

  /** Reads back a value under a partial substitution (renaming), with the occurs check and pruning. */
  def psubst(psub: PSub, v: Val): Tm = force(v) match
    case Flex(m, sp) =>
      if psub.occ.contains(m) then fail(UnifyFailure.Occurs(m))
      val (m2, sp2) = pruneFlex(psub, m, sp)
      if psub.occ.contains(m2) then fail(UnifyFailure.Occurs(m2))
      psubstSp(psub, Tm.Meta(m2), sp2)
    case Rigid(Head.Local(x), sp) =>
      psub.sub.get(x) match
        case None => fail(UnifyFailure.Escape(x))
        case Some(v) => psubstSp(psub, quote(psub.dom, v), sp)
    case Rigid(Head.Glob(id), sp) => psubstSp(psub, Tm.Global(id), sp)
    case Lam(x, i, cl) => Tm.Lam(x, i, psubst(psub.lift, inst(cl, Val.local(psub.cod))))
    case Pi(x, i, a, cl) => Tm.Pi(x, i, psubst(psub, a), psubst(psub.lift, inst(cl, Val.local(psub.cod))))
    case U0 => Tm.U0
    case U1(l) => Tm.U1(l)
    case Lift(a) => Tm.Lift(psubst(psub, a))
    case Quote(t) => Tm.Quote(psubst(psub, t))
    case RecTy(ls, env, tys) =>
      var e = env
      var p = psub
      val qs = tys.map { ty =>
        val q = psubst(p, eval(e, ty))
        e = Val.local(p.cod) :: e
        p = p.lift
        q
      }
      Tm.RecTy(ls.zip(qs))
    case Rec(fs) => Tm.Rec(fs.map((n, x) => (n, psubst(psub, x))))
    case Lit(l, st) => Tm.Lit(l, st)
    case Base(b, st) => Tm.Base(b, st)
    case RelT => Tm.RelT
    case PropT => Tm.PropT
    case Arith(op, a, b, st) => Tm.Arith(op, psubst(psub, a), psubst(psub, b), st)
    case Negate(a, st) => Tm.Negate(psubst(psub, a), st)
    case Obj(f, as) => Tm.Obj(f, as.map(psubst(psub, _)))
    case Persist(t) => Tm.Persist(psubst(psub, t))
    case FactTy(r) => Tm.FactTy(psubst(psub, r))
