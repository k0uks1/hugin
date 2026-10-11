package hugin.core

import scala.collection.mutable

/** Reduction of functions defined by clauses: a function applied to at least its arity of arguments
 *  runs its case tree; if a split meets a value that is not a constructor application (a neutral), the
 *  application stays neutral, and [[Evaluation.force]] tries again later (after metas are solved).
 *
 *  Applications to closed arguments are memoised by their normal forms: meta functions are total and
 *  pure, so this is sound, and it makes naive recursion such as `fibm (suc (suc N)) = fibm N + fibm
 *  (suc N)` linear instead of exponential (the redesign plan has memoisation by normalised arguments for
 *  families anyway). The keys are hash-consed ids of the normal forms ([[MemoKeys]]). */
trait Matching:
  self: Core =>
  import Val.*

  private val memo = mutable.HashMap.empty[(Int, List[Int]), Val]

  /** The result of applying global `id` to the spine, if it is a function that reduces. */
  def reduceFunction(id: Int, sp: Spine): Option[Val] = matchFunction(id, sp) match
    case r: Reduct => Some(if r.hit != null then appSp(r.hit.nn, r.later) else evalReduct(r))
    case Matching.Stuck => None
    case Matching.NotClauses => reduceOther(id, sp)

  /** [[reduceFunction]] of a global that is not a function defined by clauses: a primitive or a family
   *  applied to its arity reduces, anything else does not. */
  def reduceOther(id: Int, sp: Spine): Option[Val] = globals(id).kind match
    // the successor of a nat-like family applied to a numeral is the next numeral, and a constructor of
    // the meta `int` applied to one an integer
    case GlobalKind.Constructor(fam) =>
      sp match
        case List(Elim.EApp(a, Icit.Expl)) => natSuccessorOf(fam, id, a).orElse(intOfConstructor(id, a))
        case _ => None
    case GlobalKind.Primitive(op, ctors) if sp.length >= op.arity =>
      val (later, first) = sp.splitAt(sp.length - op.arity)
      if !first.forall(_.isInstanceOf[Elim.EApp]) then None
      else
        val args = first.reverse.collect { case Elim.EApp(a, i) if i == Icit.Expl || op.readsImplicit => a }
        reducePrimitive(op, ctors, args).map(appSp(_, later))
    case GlobalKind.Family(_, arity) if sp.length >= arity =>
      val (later, first) = sp.splitAt(sp.length - arity)
      val args = first.reverse.collect { case Elim.EApp(a, _) => a }
      if args.length != arity then None else familyInstance(id, args).map(appSp(_, later))
    case _ => None

  /** Global `id` applied to the spine, if it is a function defined by clauses applied to at least its
   *  arity: its memoised result, its native result on numerals (an operation of `std/nat`,
   *  [[NatArithmetic]]), or the body its case tree selects, to be evaluated ([[Reduct]]);
   *  [[Matching.Stuck]] if a split meets a neutral; [[Matching.NotClauses]] for any other global. The body
   *  is not evaluated here: [[Machine]] evaluates it, past a depth without native recursion (issue #129). */
  def matchFunction(id: Int, sp: Spine): Reduct | Matching.Stuck.type | Matching.NotClauses.type =
    globals(id).kind match
      case GlobalKind.Function(arity, Some(tree)) if sp.length >= arity =>
        val (later, first) = sp.splitAt(sp.length - arity)
        val args = first.reverse.collect { case Elim.EApp(a, _) => a }
        if args.length != arity then Matching.Stuck
        else
          // an operation of `std/nat` on numerals computes on numbers (`toInt` beyond 64 bits is stuck);
          // on anything else its clauses run (Agda's `primClauses`)
          val native = tree.native match
            case Some(n) => nativeResult(n, args)
            case None => None
          native match
            case Some(Some(v)) =>
              Matching.nativeSteps += 1
              Reduct(v, null, Nil, null, later)
            case Some(None) => Matching.Stuck
            case None => runClauses(id, tree, args, later)
      case _ => Matching.NotClauses

  /** [[matchFunction]] by the case tree of `tree`, for `args` (as many as its arity). */
  private def runClauses(id: Int, tree: FunctionBody, args: List[Val], later: Spine): Reduct | Matching.Stuck.type =
    // a native operation is not memoised: on numerals it computes in one step, and its clauses, which run
    // on anything else, take a step per constructor of an argument (the key of an open argument, stuck
    // meta code that shares values, cost a read-back at every application)
    val key =
      if tree.native.isDefined then null
      else
        closedKeyIds(args) match
          case Some(ids) => (id, ids)
          case None => null
    val hit = if key == null then null else memo.getOrElse(key, null)
    if hit != null then Reduct(hit, null, Nil, null, later)
    else
      Matching.clauseSteps += 1
      runTree(tree.tree, args.toVector, key, later)

  protected def memoise(key: (Int, List[Int]), v: Val): Unit = memo(key) = v

  /** The body selected by the case tree `tree` for the variables `env`, or [[Matching.Stuck]] if a split
   *  meets a neutral (or a value that matches no branch). A loop rather than a recursion through the
   *  splits: the JVM stack does not grow with the depth of the case tree, which is large for quoted
   *  patterns (`mirror ('( edge $X $Y :- $..B ) :: Rest)`, issue #88). */
  @scala.annotation.tailrec
  private def runTree(tree: CaseTree, env: Vector[Val], key: (Int, List[Int]) | Null, later: Spine): Reduct | Matching.Stuck.type =
    tree match
      case CaseTree.Leaf(body, size, subst, _) =>
        if env.length == size then Reduct(null, body, clauseEnv(subst, env), key, later) else Matching.Stuck
      case CaseTree.Split(level, branches) =>
        // a numeral matches `zero` or `suc` of its predecessor, in O(1) (Agda's `constructorForm`)
        natView(forceData(env(level))) match
          case Rigid(Head.Glob(c), csp) =>
            branches.find(_.ctor == c) match
              case Some(b) =>
                val args = csp.reverse.collect { case Elim.EApp(a, _) => a }
                if args.length == b.arity then runTree(b.tree, env ++ args, key, later) else Matching.Stuck
              case None => Matching.Stuck
          case _ => Matching.Stuck
      case CaseTree.SplitNat(level, fam, values, offset, above, below) =>
        natChain(forceData(env(level))) match
          case Left(m) =>
            values.find(_._1 == m) match
              case Some((_, t)) => runTree(t, env, key, later)
              case None =>
                if offset > 0 && m >= offset then runTree(above, env :+ Nat(fam, m - offset), key, later)
                else runTree(below, env, key, later)
          // successors applied `i` times to a neutral: not a numeral below `i`, at least `i`
          case Right((i, base)) =>
            if values.exists(_._1 >= i) then Matching.Stuck
            else if offset == 0 then runTree(below, env, key, later)
            else if i >= offset then runTree(above, env :+ natSuccs(natLike(fam).get._2, base, i - offset), key, later)
            else Matching.Stuck
      case CaseTree.SplitAtom(level, branches, default) =>
        atomKey(env(level)) match
          case Some(k) => runTree(branches.find(_._1 == k).map(_._2).getOrElse(default), env, key, later)
          case None => Matching.Stuck

  /** The environment of a clause's body at a leaf: the values of the clause context's variables, by the
   *  leaf's substitution `subst` over the leaf's variables `env` (mostly variables of the leaf: `σ`
   *  renames; otherwise a constructor term over them, for a variable of the clause that the leaf refines). */
  private def clauseEnv(subst: Vector[Tm], env: Vector[Val]): List[Val] =
    val size = env.length
    var bodyEnv: List[Val] = Nil
    var leafEnv: List[Val] | Null = null
    var k = 0
    while k < subst.length do
      val v = subst(k) match
        case Tm.Var(ix) => env(size - 1 - ix)
        case t =>
          if leafEnv == null then leafEnv = env.reverseIterator.toList
          eval(leafEnv.nn, t)
      bodyEnv = v :: bodyEnv
      k += 1
    bodyEnv

  /** A value forced, without the positions around it (reflected data carries the positions of the object
   *  syntax it was reified from, reference: reflection). */
  def forceData(v: Val): Val =
    val f = force(v)
    val u = Val.unloc(f)
    // forced again only if a position was removed: forcing a stuck application tries to reduce it, which
    // forces the value it splits on, so forcing twice per split doubled the work at every level of a
    // stuck value (2^depth, issue #108)
    if u eq f then f else force(u)

  /** The key of a canonical atom (a reference to an object constant, a meta literal), as split on by
   *  [[CaseTree.SplitAtom]]; `None` for a value that is not one (yet). */
  def atomKey(v: Val): Option[Tm] = forceData(v) match
    case Lit(l, Stage.S1) => Some(Tm.Lit(l, Stage.S1))
    // a numeral is an atom too: `same 3 3` reduces
    case Nat(f, n) => Some(Tm.Nat(f, n))
    // an integer as the literal it was before integers were inductive (the key of a quoted pattern's
    // literal), or as a number beyond 64 bits
    case IntNum(n) => Some(if Integers.fits64(n) then Tm.Lit(hugin.syntax.Literal.IntL(n.toLong), Stage.S1) else Tm.IntNum(n))
    case Quote(t) =>
      forceData(t) match
        case Rigid(Head.Glob(id), Nil) => Some(Tm.Quote(Tm.Global(id)))
        case _ => None
    case _ => None

object Matching:
  /** Counters for the benchmarks (docs/PERFORMANCE.md, not synchronised): the applications of functions
   *  defined by clauses that ran a case tree (memoised results not counted), and those computed by a
   *  native operation ([[NatArithmetic]]). Deterministic for a program, unlike times. */
  var clauseSteps: Long = 0
  var nativeSteps: Long = 0

  /** A split met a neutral, or a value that matches no branch: the application stays neutral. */
  case object Stuck

  /** The global is not a function defined by clauses applied to its arity. */
  case object NotClauses

/** An application of a function defined by clauses that reduces: its memoised result `hit`, or its
 *  `body` in `env`, to be memoised under `key` (if closed); then the arguments `later` beyond its arity
 *  are applied. */
final class Reduct(val hit: Val | Null, val body: Tm, val env: List[Val], val key: (Int, List[Int]) | Null, val later: Spine):
  /** What remains after the body's value, on `k`: memoise it, then apply `later`. */
  def frames(k: Machine.Frame | Null): Machine.Frame | Null =
    val withLater = Machine.elimFrames(later, k)
    if hit == null && key != null then Machine.KMemo(key.nn, withLater) else withLater
