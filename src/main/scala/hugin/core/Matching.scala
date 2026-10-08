package hugin.core

import scala.collection.mutable

/** Reduction of functions defined by clauses: a function applied to at least its arity of arguments
 *  runs its case tree; if a split meets a value that is not a constructor application (a neutral), the
 *  application stays neutral, and [[Evaluation.force]] tries again later (after metas are solved).
 *
 *  Applications to closed arguments are memoised by their normal forms: meta functions are total and
 *  pure, so this is sound, and it makes naive recursion such as `fibm (suc (suc N)) = fibm N + fibm
 *  (suc N)` linear instead of exponential (REDESIGN §6.7 plans memoisation by normalised arguments for
 *  families anyway). */
trait Matching:
  self: Core =>
  import Val.*

  private val memo = mutable.HashMap.empty[(Int, List[Tm]), Val]

  /** The result of applying global `id` to the spine, if it is a function that reduces. */
  def reduceFunction(id: Int, sp: Spine): Option[Val] = globals(id).kind match
    case GlobalKind.Function(arity, Some(tree)) if sp.length >= arity =>
      val (later, first) = sp.splitAt(sp.length - arity)
      val args = first.reverse.collect { case Elim.EApp(a, _) => a }
      if args.length != arity then None
      else
        val key = closedKey(args).map((id, _))
        key.flatMap(memo.get).orElse {
          val r = runTree(tree, args.toVector)
          for k <- key; v <- r do memo(k) = v
          r
        }.map(appSp(_, later))
    case _ => None

  private def runTree(tree: CaseTree, env: Vector[Val]): Option[Val] = tree match
    case CaseTree.Leaf(body, size, order, _, _) =>
      Option.when(env.length == size)(eval(order.reverseIterator.map(env).toList, body))
    case CaseTree.Split(level, branches) =>
      force(env(level)) match
        case Rigid(Head.Glob(c), csp) =>
          branches.find(_.ctor == c).flatMap { b =>
            val args = csp.reverse.collect { case Elim.EApp(a, _) => a }
            if args.length == b.arity then runTree(b.tree, env ++ args) else None
          }
        case _ => None

  /** The normal forms of the arguments, if they are closed (no variables, no metas, no functions). */
  private def closedKey(args: List[Val]): Option[List[Tm]] =
    val tms = args.map(quote(0, _))
    Option.when(tms.forall(closed))(tms)

  private def closed(t: Tm): Boolean = t match
    case Tm.Global(_) | Tm.Lit(_, _) | Tm.Base(_, _) | Tm.U0 | Tm.U1(_) | Tm.RelT | Tm.PropT => true
    case Tm.App(f, a, _) => closed(f) && closed(a)
    case Tm.Rec(fs) => fs.forall(f => closed(f._2))
    case Tm.Quote(a) => closedObject(a)
    case Tm.Arith(_, a, b, _) => closed(a) && closed(b)
    case _ => false

  /** Closed object code (no variables or metas). */
  private def closedObject(t: Tm): Boolean = t match
    case Tm.Var(_) | Tm.Meta(_) | Tm.AppPruning(_, _) | Tm.Lam(_, _, _) | Tm.Splice(_) => false
    case Tm.App(f, a, _) => closedObject(f) && closedObject(a)
    case Tm.Arith(_, a, b, _) => closedObject(a) && closedObject(b)
    case Tm.Obj(_, as) => as.forall(closedObject)
    case Tm.Negate(a, _) => closedObject(a)
    case Tm.Proj(a, _) => closedObject(a)
    case _ => true
