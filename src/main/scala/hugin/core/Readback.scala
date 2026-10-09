package hugin.core

/** Read-back (quotation) of values into normal forms, folded or unfolded ([[Val.Top]]), and zonking
 *  (substituting solved metas). */
trait Readback:
  self: Core =>
  import Val.*

  /** The normal form of `v` (definitions unfolded): what staging, memo keys and comparisons use. */
  def quote(l: Int, v: Val): Tm = readBack(l, v, folded = false)

  /** The read-backs of the current read-back (a call and the calls it makes), shared by value object,
   *  level and mode once the value being read back holds stuck meta code (issue #108). Meta code shares
   *  values (a function that uses its argument twice), and stuck code keeps them: `step G (step G R)`
   *  where `step` is stuck refers to `R` twice at every level, a value of linear size whose tree is
   *  exponential. Read back node by node, it took exponential time and memory (and every memo key of an
   *  application to it, [[MemoKeys]]). Read back with this sharing, its normal form is a term of the same
   *  size, whose shared subterms are the same objects. The cache is only made when a stuck application is
   *  met, so the read-back of values without stuck code (object code, data) allocates nothing more; it is
   *  dropped when the outermost call returns. */
  private var shared: java.util.IdentityHashMap[Val, (Int, Boolean, Tm)] = null
  private var readBackDepth = 0

  /** Runs `f` as one read-back: the read-backs it makes share their results (a memo key of several
   *  arguments that share values, [[MemoKeys]]). */
  def sharingReadBack[A](f: => A): A =
    readBackDepth += 1
    try f
    finally
      readBackDepth -= 1
      if readBackDepth == 0 then shared = null

  /** An application of a function, a definition or a postulate that does not reduce: stuck meta code. */
  private def stuckApplication(v: Val): Boolean = v match
    case Rigid(Head.Glob(id), sp) if sp.nonEmpty =>
      globals(id).kind match
        case _: GlobalKind.Function | _: GlobalKind.Definition | GlobalKind.Postulate => true
        case _ => false
    case _ => false

  /** Values with parts, whose read-back is worth sharing. */
  private def shareable(v: Val): Boolean = v match
    case Rigid(_, sp) => sp.nonEmpty
    case Flex(_, sp) => sp.nonEmpty
    case Top(_, sp, _) => sp.nonEmpty
    case _: Rec | _: Obj | _: Arith | _: Negate | _: Persist | _: Quote => true
    case _ => false

  /** `v` read back with definitions folded (glued evaluation, [[Val.Top]]): the smallest term, for
   *  printing, meta solutions and the terms the elaborator keeps (`zonk`). Its value is the same. */
  def quoteFolded(l: Int, v: Val): Tm = readBack(l, v, folded = true)

  private def readBack(l: Int, v: Val, folded: Boolean): Tm =
    val cache = shared
    val hit = if cache == null then null else cache.get(v)
    if hit != null && hit._1 == l && hit._2 == folded then hit._3
    else
      readBackDepth += 1
      try
        val fv = if folded then forceMetas(v) else force(v)
        // from the first stuck application on, before its parts are read back
        if shared == null && stuckApplication(fv) then shared = java.util.IdentityHashMap()
        val t = readBackForced(l, fv, folded)
        val c = shared
        if c != null && shareable(fv) then
          c.put(v, (l, folded, t))
          c.put(fv, (l, folded, t))
        t
      finally
        readBackDepth -= 1
        if readBackDepth == 0 then shared = null

  private def readBackForced(l: Int, fv: Val, folded: Boolean): Tm =
    def go(l: Int, v: Val): Tm = readBack(l, v, folded)
    fv match
      case Flex(m, sp) => quoteSp(l, Tm.Meta(m), sp, folded)
      case Top(id, sp, _) => quoteSp(l, Tm.Global(id), sp, folded)
      case Rigid(Head.Local(x), sp) => quoteSp(l, Tm.Var(l - x - 1), sp, folded)
      case Rigid(Head.Glob(id), sp) => quoteSp(l, Tm.Global(id), sp, folded)
      case Rigid(Head.Module(b, env), sp) => quoteSp(l, Tm.Module(b, env.map(go(l, _))), sp, folded)
      case Lam(x, i, cl) => Tm.Lam(x, i, go(l + 1, inst(cl, Val.local(l))))
      case Pi(x, i, a, cl) => Tm.Pi(x, i, go(l, a), go(l + 1, inst(cl, Val.local(l))))
      case U0 => Tm.U0
      case U1(k) => Tm.U1(k)
      case Lift(a) => Tm.Lift(go(l, a))
      case Quote(t) => Tm.Quote(go(l, t))
      case RecTy(ls, env, tys, rs, ds) =>
        var e = env
        var lv = l
        val qs = tys.map { ty =>
          val q = go(lv, eval(e, ty))
          e = Val.local(lv) :: e
          lv += 1
          q
        }
        Tm.RecTy(ls.zip(qs), rs, ds)
      case Rec(fs) => Tm.Rec(fs.map((n, v) => (n, go(l, v))))
      case Lit(x, st) => Tm.Lit(x, st)
      case Base(b, st) => Tm.Base(b, st)
      case RelT => Tm.RelT
      case PropT => Tm.PropT
      case Arith(op, a, b, st) => Tm.Arith(op, go(l, a), go(l, b), st)
      case Negate(a, st) => Tm.Negate(go(l, a), st)
      case Obj(f, as) => Tm.Obj(f, as.map(go(l, _)))
      case Persist(t) => Tm.Persist(go(l, t))
      case FactTy(r) => Tm.FactTy(go(l, r))

  def quoteSp(l: Int, h: Tm, sp: Spine, folded: Boolean = false): Tm = sp.reverse.foldLeft(h) { (acc, e) =>
    e match
      case Elim.EApp(a, i) => Tm.App(acc, readBack(l, a, folded), i)
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
      case Some(v) => quoteFolded(l, v)
      case None =>
        t match
          case Tm.App(f, a, i) => Tm.App(zonk(env, l, f), zonk(env, l, a), i)
          case Tm.Lam(x, i, b) => Tm.Lam(x, i, under(b))
          case Tm.Pi(x, i, a, b) => Tm.Pi(x, i, zonk(env, l, a), under(b))
          case Tm.Let(x, a, d, b) => Tm.Let(x, zonk(env, l, a), zonk(env, l, d), under(b))
          case Tm.Lift(a) => Tm.Lift(zonk(env, l, a))
          case Tm.Quote(a) => Tm.quote(zonk(env, l, a))
          case Tm.Splice(a) => Tm.splice(zonk(env, l, a))
          case Tm.Require(rs, u, a) => Tm.Require(rs, u, zonk(env, l, a))
          case Tm.Trace(f, a) => Tm.Trace(f, zonk(env, l, a))
          case Tm.RecTy(fs, rs, ds) =>
            var e = env
            var lv = l
            Tm.RecTy(
              fs.map { (n, ty) =>
                val z = zonk(e, lv, ty)
                e = Val.local(lv) :: e
                lv += 1
                (n, z)
              },
              rs,
              ds
            )
          case Tm.Rec(fs) => Tm.Rec(fs.map((n, x) => (n, zonk(env, l, x))))
          case Tm.Proj(a, lb) => Tm.Proj(zonk(env, l, a), lb)
          case Tm.Arith(op, a, b, st) => Tm.Arith(op, zonk(env, l, a), zonk(env, l, b), st)
          case Tm.Negate(a, st) => Tm.Negate(zonk(env, l, a), st)
          case Tm.Obj(f, as) => Tm.Obj(f, as.map(zonk(env, l, _)))
          case Tm.Module(b, menv) => Tm.Module(b, menv.map(zonk(env, l, _)))
          case Tm.Fresh(ns, b) =>
            val locals = ns.indices.map(i => Val.local(l + i)).reverse.toList
            Tm.Fresh(ns, zonk(locals ++ env, l + ns.length, b))
          case Tm.Persist(a) => Tm.Persist(zonk(env, l, a))
          case Tm.FactTy(a) => Tm.FactTy(zonk(env, l, a))
          case other => other
