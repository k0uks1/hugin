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

  /** How many applications of functions defined by clauses are running, nested (issue #129). */
  private var depth = 0

  /** The result of applying global `id` to the spine, if it is a function that reduces. */
  def reduceFunction(id: Int, sp: Spine): Option[Val] = globals(id).kind match
    case GlobalKind.Function(arity, Some(tree)) if sp.length >= arity =>
      val (later, first) = sp.splitAt(sp.length - arity)
      val args = first.reverse.collect { case Elim.EApp(a, _) => a }
      if args.length != arity then None
      else
        // straight-line code rather than `Option` combinators: a meta function's recursion nests
        // `eval` -> `reduceFunction` -> `runTree` -> `eval` once per call, so every frame here is paid
        // once per level of the recursion (issue #88)
        val key = closedKeyIds(args) match
          case Some(ids) => (id, ids)
          case None => null
        val hit = if key == null then null else memo.getOrElse(key, null)
        val r =
          if hit != null then hit
          else
            val v = nested(tree, args.toVector)
            if key != null && v != null then memo(key) = v
            v
        if r == null then None else Some(appSp(r, later))
    case GlobalKind.Primitive(op, ctors) if sp.length >= op.arity =>
      val (later, first) = sp.splitAt(sp.length - op.arity)
      if !first.forall(_.isInstanceOf[Elim.EApp]) then None
      else reducePrimitive(op, ctors, first.reverse.collect { case Elim.EApp(a, Icit.Expl) => a }).map(appSp(_, later))
    case GlobalKind.Family(_, arity) if sp.length >= arity =>
      val (later, first) = sp.splitAt(sp.length - arity)
      val args = first.reverse.collect { case Elim.EApp(a, _) => a }
      if args.length != arity then None else familyInstance(id, args).map(appSp(_, later))
    case _ => None

  /** [[runTree]] one level deeper in the recursion of meta functions: a meta function recursing over a
   *  list nests one level per element, and every [[hugin.util.StackSegments.levels]] levels continue on
   *  a new stack segment, so the depth of the recursion is not bounded by the caller's stack (issue #129). */
  private def nested(tree: CaseTree, env: Vector[Val]): Val | Null =
    depth += 1
    try hugin.util.StackSegments.deeper(depth)(runTree(tree, env))
    finally depth -= 1

  /** The value of the case tree `tree` for the variables `env`, or `null` if a split meets a neutral (or a
   *  value that matches no branch). A loop rather than a recursion through the splits: the JVM stack a
   *  meta function's recursion uses per level does not grow with the depth of its case tree, which is
   *  large for quoted patterns (`mirror ('( edge $X $Y :- $..B ) :: Rest)`, issue #88). */
  @scala.annotation.tailrec
  private def runTree(tree: CaseTree, env: Vector[Val]): Val | Null = tree match
    case CaseTree.Leaf(body, size, order, _, _) =>
      if env.length == size then eval(order.reverseIterator.map(env).toList, body) else null
    case CaseTree.Split(level, branches) =>
      forceData(env(level)) match
        case Rigid(Head.Glob(c), csp) =>
          branches.find(_.ctor == c) match
            case Some(b) =>
              val args = csp.reverse.collect { case Elim.EApp(a, _) => a }
              if args.length == b.arity then runTree(b.tree, env ++ args) else null
            case None => null
        case _ => null
    case CaseTree.SplitAtom(level, branches, default) =>
      atomKey(env(level)) match
        case Some(k) => runTree(branches.find(_._1 == k).map(_._2).getOrElse(default), env)
        case None => null

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
