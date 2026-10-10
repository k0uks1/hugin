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
    case Matching.NotClauses =>
      globals(id).kind match
        case GlobalKind.Primitive(op, ctors) if sp.length >= op.arity =>
          val (later, first) = sp.splitAt(sp.length - op.arity)
          if !first.forall(_.isInstanceOf[Elim.EApp]) then None
          else reducePrimitive(op, ctors, first.reverse.collect { case Elim.EApp(a, Icit.Expl) => a }).map(appSp(_, later))
        case GlobalKind.Family(_, arity) if sp.length >= arity =>
          val (later, first) = sp.splitAt(sp.length - arity)
          val args = first.reverse.collect { case Elim.EApp(a, _) => a }
          if args.length != arity then None else familyInstance(id, args).map(appSp(_, later))
        case _ => None

  /** Global `id` applied to the spine, if it is a function defined by clauses applied to at least its
   *  arity: its memoised result, or the body its case tree selects, to be evaluated ([[Reduct]]);
   *  [[Matching.Stuck]] if a split meets a neutral; [[Matching.NotClauses]] for any other global. The body
   *  is not evaluated here: [[Machine]] evaluates it without native recursion per call (issue #129). */
  def matchFunction(id: Int, sp: Spine): Reduct | Matching.Stuck.type | Matching.NotClauses.type =
    globals(id).kind match
      case GlobalKind.Function(arity, Some(tree)) if sp.length >= arity =>
        val (later, first) = sp.splitAt(sp.length - arity)
        val args = first.reverse.collect { case Elim.EApp(a, _) => a }
        if args.length != arity then Matching.Stuck
        else
          val key = closedKeyIds(args) match
            case Some(ids) => (id, ids)
            case None => null
          val hit = if key == null then null else memo.getOrElse(key, null)
          if hit != null then Reduct(hit, null, Nil, null, later)
          else runTree(tree, args.toVector, key, later)
      case _ => Matching.NotClauses

  protected def memoise(key: (Int, List[Int]), v: Val): Unit = memo(key) = v

  /** The body selected by the case tree `tree` for the variables `env`, or [[Matching.Stuck]] if a split
   *  meets a neutral (or a value that matches no branch). A loop rather than a recursion through the
   *  splits: the JVM stack does not grow with the depth of the case tree, which is large for quoted
   *  patterns (`mirror ('( edge $X $Y :- $..B ) :: Rest)`, issue #88). */
  @scala.annotation.tailrec
  private def runTree(tree: CaseTree, env: Vector[Val], key: (Int, List[Int]) | Null, later: Spine): Reduct | Matching.Stuck.type =
    tree match
      case CaseTree.Leaf(body, size, order, _, _) =>
        if env.length == size then Reduct(null, body, order.reverseIterator.map(env).toList, key, later) else Matching.Stuck
      case CaseTree.Split(level, branches) =>
        forceData(env(level)) match
          case Rigid(Head.Glob(c), csp) =>
            branches.find(_.ctor == c) match
              case Some(b) =>
                val args = csp.reverse.collect { case Elim.EApp(a, _) => a }
                if args.length == b.arity then runTree(b.tree, env ++ args, key, later) else Matching.Stuck
              case None => Matching.Stuck
          case _ => Matching.Stuck
      case CaseTree.SplitAtom(level, branches, default) =>
        atomKey(env(level)) match
          case Some(k) => runTree(branches.find(_._1 == k).map(_._2).getOrElse(default), env, key, later)
          case None => Matching.Stuck

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
    case Quote(t) =>
      forceData(t) match
        case Rigid(Head.Glob(id), Nil) => Some(Tm.Quote(Tm.Global(id)))
        case _ => None
    case _ => None

object Matching:
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
