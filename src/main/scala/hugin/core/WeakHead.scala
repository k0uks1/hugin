package hugin.core

/** Weak-head evaluation on demand, for index unification, splitting and coverage (issue #195).
 *
 *  Evaluation ([[Machine]]) is strict: applying a function defined by clauses to closed arguments computes
 *  its whole value. Unification only needs the head of each side, and descends into arguments on demand
 *  (Cockx & Abel's unifier in Agda, `Agda.TypeChecking.Rules.LHS.Unify`, works on `reduce`d terms; Lean's
 *  and Rocq's conversion checks compare weak-head normal forms first). Normalising instead made coverage
 *  of `vec int (double n)` with `n := 9223372036854775807` take 2^63 steps, although one step of `double`
 *  exposes a successor that refutes `vnil`.
 *
 *  Here an application of a function defined by clauses is *delayed*: it stays the neutral
 *  `Rigid(Head.Glob(f), sp)` it is before its arguments are known, a value that [[Evaluation.force]] and
 *  read-back evaluate as usual, so a delayed value means what its strict evaluation means and every other
 *  consumer stays correct. [[whnf]] runs one function at the head at a time, its case tree splitting on
 *  arguments evaluated to weak-head form only ([[Matching.matchWeak]]), and its body evaluated with the
 *  applications in it delayed ([[evalWeak]]). Numerals keep their O(1) views: a successor is a head
 *  ([[Val.NatAdd]], [[Naturals.natView]]), and an operation of `std/nat` on numerals computes natively. */
trait WeakHead:
  self: Core =>
  import Val.*

  /** `v` in weak-head normal form: the function applications, folded definitions and solved metas at its
   *  head are run or unfolded until its head is a constructor, a numeral or successor, a variable or a
   *  stuck application; its arguments are not evaluated. The head is the head of its normal form. */
  @scala.annotation.tailrec
  final def whnf(v: Val): Val = v match
    case Top(_, _, u) => whnf(u.value)
    case Flex(m, sp) =>
      metas(m).solution match
        case Some(s) => whnf(appSpWeak(s, sp))
        case None => v
    case Rigid(Head.Glob(id), sp) =>
      globals(id).kind match
        case GlobalKind.Definition(_, d) => whnf(appSpWeak(d, sp))
        case GlobalKind.Function(arity, Some(tree)) =>
          if sp.length < arity then v
          else
            val (later, first) = sp.splitAt(sp.length - arity)
            if !first.forall(_.isInstanceOf[Elim.EApp]) then v
            else
              matchWeak(tree, first.reverse.collect { case Elim.EApp(a, _) => a }, later) match
                case r: Reduct => whnf(appSpWeak(if r.hit != null then r.hit.nn else evalWeak(r.env, r.body), r.later))
                case Matching.Stuck => v
        case _: GlobalKind.Function | _: GlobalKind.Opaque | GlobalKind.Postulate => v
        // constructors (numerals), primitives and families reduce as evaluation reduces them
        case _ => force(v)
    // a successor is a head; an offset whose base is (already) a numeral or an offset is added up
    case NatAdd(_, _, _) => numeral(v)
    case _: Rigid | _: Obj | _: Arith | _: Negate | _: Persist => force(v)
    case other => other

  /** [[whnf]] without the positions around the value ([[Matching.forceData]]). */
  final def whnfData(v: Val): Val =
    val w = whnf(v)
    val u = Val.unloc(w)
    if u eq w then w else whnf(u)

  /** The value of `t` in `env`, with the applications of functions defined by clauses delayed ([[appWeak]]);
   *  other compound terms are evaluated as by [[Machine.eval]]. */
  final def evalWeak(env: List[Val], t: Tm): Val = t match
    case Tm.App(f, a, i) =>
      val fv = evalWeak(env, f)
      appWeak(fv, argument(evalWeak(env, a)), i)
    case Tm.Let(_, _, d, b) => evalWeak(evalWeak(env, d) :: env, b)
    case Tm.NatAdd(f, b, k) => natAdd(f, evalWeak(env, b), k)
    case Tm.Arith(op, a, b, st) =>
      val x = evalWeak(env, a)
      arith(op, x, evalWeak(env, b), st)
    case Tm.Negate(a, st) => negate(evalWeak(env, a), st)
    case Tm.Persist(a) => persist(evalWeak(env, a))
    case Tm.Splice(a) => vSplice(evalWeak(env, a))
    case Tm.Proj(a, l) => proj(evalWeak(env, a), l)
    case _ => eval(env, t)

  /** `f` applied to `a`, an application of a function defined by clauses delayed: run by [[whnf]] (or by
   *  [[Evaluation.force]]) when its value is needed. */
  final def appWeak(f: Val, a: Val, i: Icit): Val = f match
    case Lam(_, _, cl) => evalWeak(a :: cl.env, cl.body)
    case Obj(ObjForm.Loc(_), List(g)) => appWeak(g, a, i)
    case Rigid(h @ Head.Glob(id), sp) if globals(id).kind.isInstanceOf[GlobalKind.Function] => Rigid(h, Elim.EApp(a, i) :: sp)
    case Top(id, sp, u) => Top(id, Elim.EApp(a, i) :: sp, Unfold(appWeak(u.value, a, i)))
    case _ => app(f, a, i)

  final def appSpWeak(v: Val, sp: Spine): Val =
    if sp.isEmpty then v
    else
      sp.reverse.foldLeft(v) { (acc, e) =>
        e match
          case Elim.EApp(a, i) => appWeak(acc, a, i)
          case Elim.ESplice => vSplice(acc)
          case Elim.EProj(l) => proj(acc, l)
      }

  /** [[Naturals.natChain]] by weak-head steps, cut once `limit` successors are taken off: then `Right` with
   *  the rest, which may have more successors (a split that tells numerals apart up to `limit` needs no
   *  more, [[Matching.matchWeak]]). */
  final def natChainWeak(v: Val, limit: BigInt): Either[BigInt, (BigInt, Val)] =
    var i = BigInt(0)
    var cur = whnf(v)
    var result: Either[BigInt, (BigInt, Val)] | Null = null
    while result == null do
      cur match
        case Nat(_, m) => result = Left(m + i)
        case NatAdd(_, b, k) =>
          i += k
          if i >= limit then result = Right((i, b)) else cur = whnf(b)
        case Rigid(Head.Glob(c), List(Elim.EApp(a, Icit.Expl))) if isSuccessor(c) =>
          i += 1
          if i >= limit then result = Right((i, a)) else cur = whnf(a)
        case Rigid(Head.Glob(c), Nil) if constantOf(c) => result = Left(i)
        case other => result = Right((i, other))
    result.nn

  /** `v` with the variables of levels below `values.length` replaced by their values, without evaluating:
   *  the applications that the substitution unblocks stay delayed (what [[elab.SplitProblem.norm]] does,
   *  where evaluation and read-back normalised the whole value). Folded definitions and solved metas are
   *  unfolded, as read-back unfolds them. */
  final def substitute(values: Vector[Val], v: Val): Val =
    val n = values.length
    def go(v: Val): Val = v match
      case Rigid(Head.Local(x), sp) => appSpWeak(if x < n then values(x) else v, goSp(sp))
      case Rigid(Head.Glob(id), sp) => if sp.isEmpty then v else Rigid(Head.Glob(id), goSp(sp))
      case Rigid(Head.Module(b, env), sp) => Rigid(Head.Module(b, env.map(go)), goSp(sp))
      case Flex(m, sp) =>
        metas(m).solution match
          case Some(s) => go(appSpWeak(s, sp))
          case None => Flex(m, goSp(sp))
      case Top(_, _, u) => go(u.value)
      case Lam(x, i, cl) => Lam(x, i, Closure(cl.env.map(go), cl.body))
      case Pi(x, i, a, cl) => Pi(x, i, go(a), Closure(cl.env.map(go), cl.body))
      case r: RecTy => r.copy(env = r.env.map(go))
      case Rec(fs) => Rec(fs.map((l, x) => (l, go(x))))
      case Lift(a) => Lift(go(a))
      case Quote(t) => vQuote(go(t))
      case NatAdd(f, b, k) => natAdd(f, go(b), k)
      case Arith(op, a, b, st) => arith(op, go(a), go(b), st)
      case Negate(a, st) => negate(go(a), st)
      case Obj(form, as) => if as.isEmpty then v else Obj(form, as.map(go))
      case Persist(t) => persist(go(t))
      case FactTy(r) => FactTy(go(r))
      case U0 | _: U1 | _: Lit | _: Base | _: Nat | RelT | PropT => v
    def goSp(sp: Spine): Spine = sp.map {
      case Elim.EApp(a, i) => Elim.EApp(go(a), i)
      case e => e
    }
    go(v)

  /** Whether the variable of level `l` occurs in `v` as it is, unevaluated. If not, it does not occur in its
   *  normal form either (evaluation adds no free variables): what an occurs check can decide without
   *  normalising. */
  final def mentions(l: Int, v: Val): Boolean =
    def sp(s: Spine): Boolean = s.exists {
      case Elim.EApp(a, _) => go(a)
      case _ => false
    }
    def go(v: Val): Boolean = v match
      case Rigid(Head.Local(x), s) => x == l || sp(s)
      case Rigid(Head.Glob(_), s) => sp(s)
      case Rigid(Head.Module(_, env), s) => env.exists(go) || sp(s)
      case Flex(m, s) => metas(m).solution.exists(go) || sp(s)
      case Top(_, s, _) => sp(s)
      case Lam(_, _, cl) => cl.env.exists(go)
      case Pi(_, _, a, cl) => go(a) || cl.env.exists(go)
      case r: RecTy => r.env.exists(go)
      case Rec(fs) => fs.exists(f => go(f._2))
      case Lift(a) => go(a)
      case Quote(t) => go(t)
      case NatAdd(_, b, _) => go(b)
      case Arith(_, a, b, _) => go(a) || go(b)
      case Negate(a, _) => go(a)
      case Obj(_, as) => as.exists(go)
      case Persist(t) => go(t)
      case FactTy(r) => go(r)
      case U0 | _: U1 | _: Lit | _: Base | _: Nat | RelT | PropT => false
    go(v)

  /** Whether `a` and `b` (values at level `l`) have the same normal form, `quote(l, a) == quote(l, b)`,
   *  compared by weak-head forms from the outside in, so that a difference near the head is found without
   *  normalising either side; what the comparison does not handle itself is read back. */
  final def sameWeak(l: Int, a: Val, b: Val): Boolean =
    if a == b then true
    else
      val x = whnf(a)
      val y = whnf(b)
      (x, y) match
        case _ if isNumeral(x) || isNumeral(y) => sameNat(l, x, y)
        case (Rigid(h1 @ (_: Head.Local | _: Head.Glob), sp1), Rigid(h2 @ (_: Head.Local | _: Head.Glob), sp2)) =>
          h1 == h2 && sameSpine(l, sp1, sp2)
        case (_: Rigid, _: Rigid) => quote(l, x) == quote(l, y)
        case (Rigid(_, _), _) | (_, Rigid(_, _)) => false
        case (Flex(m1, sp1), Flex(m2, sp2)) => m1 == m2 && sameSpine(l, sp1, sp2)
        case (Lit(v1, s1), Lit(v2, s2)) => v1 == v2 && s1 == s2
        case _ => quote(l, x) == quote(l, y)

  private def isNumeral(v: Val): Boolean = v.isInstanceOf[Nat] || v.isInstanceOf[NatAdd]

  private def sameSpine(l: Int, sp1: Spine, sp2: Spine): Boolean =
    sp1.length == sp2.length && sp1.zip(sp2).forall {
      case (Elim.EApp(a, i), Elim.EApp(b, j)) => i == j && sameWeak(l, a, b)
      case (Elim.ESplice, Elim.ESplice) => true
      case (Elim.EProj(p), Elim.EProj(q)) => p == q
      case _ => false
    }

  /** [[sameWeak]] of weak-head forms one of which is a numeral or a successor: the successors are taken off
   *  both sides, a base evaluated to weak-head form only when its side has none left. */
  private def sameNat(l: Int, x: Val, y: Val): Boolean =
    // a side: `i` successors over `r` (`null`: zero), `done` once `r` is in weak-head form and no numeral
    def parts(w: Val): (BigInt, Val | Null, Boolean) = w match
      case Nat(_, n) => (n, null, true)
      case NatAdd(_, b, k) => (k, b, false)
      case other => (BigInt(0), other, true)
    var (i, ra, aDone) = parts(x)
    var (j, rb, bDone) = parts(y)
    var more = true
    var same = false
    while more do
      val m = i.min(j)
      i -= m
      j -= m
      if i == 0 && j == 0 && !aDone && !bDone && ra == rb then
        // the same value under the same number of successors
        same = true
        more = false
      else if i == 0 && !aDone then
        val w = whnf(ra.nn)
        if isNumeral(w) then
          val (i1, r1, d1) = parts(w)
          i = i1; ra = r1; aDone = d1
        else
          ra = w; aDone = true
      else if j == 0 && !bDone then
        val w = whnf(rb.nn)
        if isNumeral(w) then
          val (j1, r1, d1) = parts(w)
          j = j1; rb = r1; bDone = d1
        else
          rb = w; bDone = true
      else more = false
    if same then true
    else if i != 0 || j != 0 then false
    else if ra == null || rb == null then ra == null && rb == null
    else sameWeak(l, ra.nn, rb.nn)

  /** Steps of evaluation (in polls of [[Machine.cancellation]]) that a diagnostic may spend on the normal
   *  form of a value it shows ([[quoteShown]]). */
  private inline val ShowPolls = 64

  /** The normal form of `v` (folded, as [[Printing.showVal]] shows it, if `folded`) for a diagnostic, if it
   *  is cheap to compute; otherwise `v` read back as it is, its delayed applications unevaluated
   *  ([[quoteWeak]]): `double 9223372036854775807` rather than a numeral that takes 2^63 steps. */
  final def quoteShown(l: Int, v: Val, folded: Boolean = false): Tm =
    withinPolls(ShowPolls)(if folded then quoteFolded(l, v) else quote(l, v)).getOrElse(quoteWeak(l, v))

  /** `v` read back without evaluating anything: delayed applications stay applications. */
  final def quoteWeak(l: Int, v: Val): Tm =
    def spine(l: Int, h: Tm, sp: Spine): Tm = sp.reverse.foldLeft(h) { (acc, e) =>
      e match
        case Elim.EApp(a, i) => Tm.App(acc, go(l, a), i)
        case Elim.ESplice => Tm.Splice(acc)
        case Elim.EProj(lb) => Tm.Proj(acc, lb)
    }
    def under(l: Int, cl: Closure): Tm = go(l + 1, evalWeak(Val.local(l) :: cl.env, cl.body))
    def go(l: Int, v: Val): Tm = v match
      case Flex(m, sp) =>
        metas(m).solution match
          case Some(s) => go(l, appSpWeak(s, sp))
          case None => spine(l, Tm.Meta(m), sp)
      case Top(id, sp, _) => spine(l, Tm.Global(id), sp)
      case Rigid(Head.Local(x), sp) => spine(l, Tm.Var(l - x - 1), sp)
      case Rigid(Head.Glob(id), sp) => spine(l, Tm.Global(id), sp)
      case Rigid(Head.Module(b, env), sp) => spine(l, Tm.Module(b, env.map(go(l, _))), sp)
      case Lam(x, i, cl) => Tm.Lam(x, i, under(l, cl))
      case Pi(x, i, a, cl) => Tm.Pi(x, i, go(l, a), under(l, cl))
      case U0 => Tm.U0
      case U1(k) => Tm.U1(k)
      case Lift(a) => Tm.Lift(go(l, a))
      case Quote(t) => Tm.Quote(go(l, t))
      case RecTy(ls, env, tys, rs, ds) =>
        var e = env
        var lv = l
        val qs = tys.map { ty =>
          val q = go(lv, evalWeak(e, ty))
          e = Val.local(lv) :: e
          lv += 1
          q
        }
        Tm.RecTy(ls.zip(qs), rs, ds)
      case Rec(fs) => Tm.Rec(fs.map((n, x) => (n, go(l, x))))
      case Lit(x, st) => Tm.Lit(x, st)
      case Nat(f, n) => Tm.Nat(f, n)
      case NatAdd(f, b, k) =>
        numeral(v) match
          case NatAdd(_, b1, k1) => Tm.NatAdd(f, go(l, b1), k1)
          case other => go(l, other)
      case Base(b, st) => Tm.Base(b, st)
      case RelT => Tm.RelT
      case PropT => Tm.PropT
      case Arith(op, a, b, st) => Tm.Arith(op, go(l, a), go(l, b), st)
      case Negate(a, st) => Tm.Negate(go(l, a), st)
      case Obj(f, as) => Tm.Obj(f, as.map(go(l, _)))
      case Persist(t) => Tm.Persist(go(l, t))
      case FactTy(r) => Tm.FactTy(go(l, r))
    go(l, v)
