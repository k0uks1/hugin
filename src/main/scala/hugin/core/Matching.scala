package hugin.core

import scala.collection.mutable

/** Reduction of functions defined by clauses: a function applied to at least its arity of arguments
 *  runs its case tree; if a split meets a value that is not a constructor application (a neutral), the
 *  application stays neutral, and [[Evaluation.force]] tries again later (after metas are solved).
 *
 *  Applications to closed arguments are memoised by their normal forms: meta functions are total and
 *  pure, so this is sound, and it makes naive recursion such as `fibm (suc (suc N)) = fibm N + fibm
 *  (suc N)` linear instead of exponential (REDESIGN §6.7 plans memoisation by normalised arguments for
 *  families anyway). The keys are hash-consed ids of the normal forms ([[MemoKeys]]). */
trait Matching:
  self: Core =>
  import Val.*

  private val memo = mutable.HashMap.empty[(Int, List[Int]), Val]

  /** The result of applying global `id` to the spine, if it is a function that reduces. */
  def reduceFunction(id: Int, sp: Spine): Option[Val] = globals(id).kind match
    case GlobalKind.Function(arity, Some(tree)) if sp.length >= arity =>
      val (later, first) = sp.splitAt(sp.length - arity)
      val args = first.reverse.collect { case Elim.EApp(a, _) => a }
      if args.length != arity then None
      else
        val key = closedKeyIds(args).map((id, _))
        key.flatMap(memo.get).orElse {
          val r = runTree(tree, args.toVector)
          for k <- key; v <- r do memo(k) = v
          r
        }.map(appSp(_, later))
    case GlobalKind.Primitive(op, ctors) if sp.length >= op.arity =>
      val (later, first) = sp.splitAt(sp.length - op.arity)
      if !first.forall(_.isInstanceOf[Elim.EApp]) then None
      else reducePrimitive(op, ctors, first.reverse.collect { case Elim.EApp(a, Icit.Expl) => a }).map(appSp(_, later))
    case GlobalKind.Family(_, arity) if sp.length >= arity =>
      val (later, first) = sp.splitAt(sp.length - arity)
      val args = first.reverse.collect { case Elim.EApp(a, _) => a }
      if args.length != arity then None else familyInstance(id, args).map(appSp(_, later))
    case _ => None

  private def runTree(tree: CaseTree, env: Vector[Val]): Option[Val] = tree match
    case CaseTree.Leaf(body, size, order, _, _) =>
      Option.when(env.length == size)(eval(order.reverseIterator.map(env).toList, body))
    case CaseTree.Split(level, branches) =>
      forceData(env(level)) match
        case Rigid(Head.Glob(c), csp) =>
          branches.find(_.ctor == c).flatMap { b =>
            val args = csp.reverse.collect { case Elim.EApp(a, _) => a }
            if args.length == b.arity then runTree(b.tree, env ++ args) else None
          }
        case _ => None
    case CaseTree.SplitAtom(level, branches, default) =>
      atomKey(env(level)).flatMap(k => runTree(branches.find(_._1 == k).map(_._2).getOrElse(default), env))

  /** A value forced, without the positions around it (reflected data carries the positions of the object
   *  syntax it was reified from, REDESIGN §6.8). */
  def forceData(v: Val): Val = force(Val.unloc(force(v)))

  /** The key of a canonical atom (a reference to an object constant, a meta literal), as split on by
   *  [[CaseTree.SplitAtom]]; `None` for a value that is not one (yet). */
  def atomKey(v: Val): Option[Tm] = forceData(v) match
    case Lit(l, Stage.S1) => Some(Tm.Lit(l, Stage.S1))
    case Quote(t) =>
      forceData(t) match
        case Rigid(Head.Glob(id), Nil) => Some(Tm.Quote(Tm.Global(id)))
        case _ => None
    case _ => None
