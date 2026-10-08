package hugin.core

/** Read-back (quotation) of values into normal forms, and zonking (substituting solved metas). */
trait Readback:
  self: Core =>
  import Val.*

  def quote(l: Int, v: Val): Tm = force(v) match
    case Flex(m, sp) => quoteSp(l, Tm.Meta(m), sp)
    case Rigid(Head.Local(x), sp) => quoteSp(l, Tm.Var(l - x - 1), sp)
    case Rigid(Head.Glob(id), sp) => quoteSp(l, Tm.Global(id), sp)
    case Lam(x, i, cl) => Tm.Lam(x, i, quote(l + 1, inst(cl, Val.local(l))))
    case Pi(x, i, a, cl) => Tm.Pi(x, i, quote(l, a), quote(l + 1, inst(cl, Val.local(l))))
    case U0 => Tm.U0
    case U1(k) => Tm.U1(k)
    case Lift(a) => Tm.Lift(quote(l, a))
    case Quote(t) => Tm.Quote(quote(l, t))
    case RecTy(ls, env, tys) =>
      var e = env
      var lv = l
      val qs = tys.map { ty =>
        val q = quote(lv, eval(e, ty))
        e = Val.local(lv) :: e
        lv += 1
        q
      }
      Tm.RecTy(ls.zip(qs))
    case Rec(fs) => Tm.Rec(fs.map((n, v) => (n, quote(l, v))))
    case Lit(x, st) => Tm.Lit(x, st)
    case Base(b, st) => Tm.Base(b, st)
    case RelT => Tm.RelT
    case PropT => Tm.PropT
    case Arith(op, a, b, st) => Tm.Arith(op, quote(l, a), quote(l, b), st)
    case Negate(a, st) => Tm.Negate(quote(l, a), st)
    case Obj(f, as) => Tm.Obj(f, as.map(quote(l, _)))
    case Persist(t) => Tm.Persist(quote(l, t))
    case FactTy(r) => Tm.FactTy(quote(l, r))

  def quoteSp(l: Int, h: Tm, sp: Spine): Tm = sp.reverse.foldLeft(h) { (acc, e) =>
    e match
      case Elim.EApp(a, i) => Tm.App(acc, quote(l, a), i)
      case Elim.ESplice => Tm.Splice(acc)
      case Elim.EProj(lb) => Tm.Proj(acc, lb)
  }

  /** The normal form of a term in an environment of `env.length` bound variables. */
  def nf(env: List[Val], t: Tm): Tm = quote(env.length, eval(env, t))

  /** Substitutes solved metas (and reduces the applications they head), leaving everything else as
   *  elaborated: inserted quotes, splices and implicit arguments stay visible. */
  def zonk(env: List[Val], l: Int, t: Tm): Tm =
    def under(b: Tm) = zonk(Val.local(l) :: env, l + 1, b)
    def metaHeaded(t: Tm): Option[Val] = t match
      case Tm.Meta(m) => metas(m).solution
      case Tm.AppPruning(Tm.Meta(m), pr) => metas(m).solution.map(appPruning(env, _, pr))
      case Tm.App(f, a, i) => metaHeaded(f).map(app(_, eval(env, a), i))
      case _ => None
    metaHeaded(t) match
      case Some(v) => quote(l, v)
      case None =>
        t match
          case Tm.App(f, a, i) => Tm.App(zonk(env, l, f), zonk(env, l, a), i)
          case Tm.Lam(x, i, b) => Tm.Lam(x, i, under(b))
          case Tm.Pi(x, i, a, b) => Tm.Pi(x, i, zonk(env, l, a), under(b))
          case Tm.Let(x, a, d, b) => Tm.Let(x, zonk(env, l, a), zonk(env, l, d), under(b))
          case Tm.Lift(a) => Tm.Lift(zonk(env, l, a))
          case Tm.Quote(a) => Tm.quote(zonk(env, l, a))
          case Tm.Splice(a) => Tm.splice(zonk(env, l, a))
          case Tm.RecTy(fs) =>
            var e = env
            var lv = l
            Tm.RecTy(fs.map { (n, ty) =>
              val z = zonk(e, lv, ty)
              e = Val.local(lv) :: e
              lv += 1
              (n, z)
            })
          case Tm.Rec(fs) => Tm.Rec(fs.map((n, x) => (n, zonk(env, l, x))))
          case Tm.Proj(a, lb) => Tm.Proj(zonk(env, l, a), lb)
          case Tm.Arith(op, a, b, st) => Tm.Arith(op, zonk(env, l, a), zonk(env, l, b), st)
          case Tm.Negate(a, st) => Tm.Negate(zonk(env, l, a), st)
          case Tm.Obj(f, as) => Tm.Obj(f, as.map(zonk(env, l, _)))
          case Tm.Fresh(ns, b) =>
            val locals = ns.indices.map(i => Val.local(l + i)).reverse.toList
            Tm.Fresh(ns, zonk(locals ++ env, l + ns.length, b))
          case Tm.Persist(a) => Tm.Persist(zonk(env, l, a))
          case Tm.FactTy(a) => Tm.FactTy(zonk(env, l, a))
          case other => other
