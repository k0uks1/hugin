package hugin.core

import scala.collection.mutable

/** Keys of the memo of closed meta applications ([[Matching.reduceFunction]]) in amortised constant time.
 *
 *  The key of an application is the normal forms of its arguments (if they are closed). Computing them
 *  by read-back on every reduction costs the size of the arguments each time: a meta function recursing
 *  over a list of `n` items (the module a `%demand` rewrites) reads back the rest of the list at every
 *  step, O(n²) time, and the memo holds O(n²) terms. Two techniques of Lean 4 (whose `Expr` nodes carry
 *  their hash, and whose caches are keyed by them; `ShareCommon` hash-conses terms) make this linear:
 *
 *  - **Read-back cached per value object** for *stable data*: a value whose normal form cannot change
 *    while the core lives — literals, base types and sorts, applications of heads that never reduce
 *    ([[stableHead]]: constructors, inductive types, object constants, partially applied families) to
 *    stable data, object code over stable data, and records and quotes of it. No forcing is involved in
 *    reading them back (no metas, whose solutions may be undone, no function or definition that a later
 *    declaration may make reduce), so the cached term is exactly what `quote(0, v)` gives at any time. Any other value is read back with `quote` as
 *    before, uncached.
 *  - **Hash-consed ids** of the normal forms: a term gets an id from its case and the ids of its
 *    subterms (other fields as they are), cached per term object, so equal terms get the same id and
 *    different terms different ids, and comparing or hashing a key costs its number of arguments.
 *
 *  So a key is a list of ids that are equal exactly when the normal forms are: the memo hits and misses
 *  as before, and evaluation (including the fresh object variables it creates) is unchanged. */
trait MemoKeys:
  self: Core =>

  private val readBack = java.util.IdentityHashMap[Val, Tm]()
  private val termIds = java.util.IdentityHashMap[Tm, Integer]()
  private val nodeIds = mutable.HashMap.empty[Any, Int]
  private val closedIds = mutable.HashMap.empty[Int, Boolean]

  /** The normal forms of the arguments, if they are closed (no variables, no metas, no functions). */
  def closedKey(args: List[Val]): Option[List[Tm]] =
    val tms = args.map(a => quoteKey(a)._1)
    Option.when(tms.forall(closedId))(tms)

  /** The ids of the normal forms of `args`, if they are all closed ([[closedKey]]). */
  def closedKeyIds(args: List[Val]): Option[List[Int]] = closedKey(args).map(_.map(termId))

  /** Whether the global `id` applied to `n` arguments is a head that never reduces, now or later: a
   *  constructor, an inductive type or `Sym` (kinds never changed); a declared object constant (kinds
   *  never changed); a pending object constant without arguments (completing its declaration may make it
   *  a family, or a derived constant may become one, [[Primitives]], but a family reduces only when
   *  applied to its arity); a family applied to fewer arguments than its arity. */
  private def stableHead(id: Int, n: Int): Boolean =
    val g = globals(id)
    g.kind match
      case _: GlobalKind.Constructor | _: GlobalKind.Inductive | GlobalKind.Symbols => true
      case _: GlobalKind.Object => !g.pending || n == 0
      case GlobalKind.Family(_, arity) => n < arity
      case _ => false

  /** The depth of recursion after which the walks below continue with an explicit stack: a long list is
   *  a deep value or term (`x1 :: (x2 :: …)`), and the keys of a meta function recursing over it are
   *  computed at every step (issue #88). Shallow values, almost all, keep the cheaper recursion. */
  private val Deep = 200

  /** `quote(0, v)`, and whether `v` is stable data (then it is cached for `v`). */
  private def quoteKey(v: Val): (Tm, Boolean) = quoteKeyAt(v, 0)

  private def quoteKeyAt(v: Val, depth: Int): (Tm, Boolean) =
    val cached = readBack.get(v)
    if cached != null then (cached, true)
    else if depth > Deep then quoteKeyDeep(v)
    else
      val d = depth + 1
      val (t, stable) = v match
        case Val.Lit(l, st) => (Tm.Lit(l, st), true)
        case Val.Base(b, st) => (Tm.Base(b, st), true)
        case Val.U0 => (Tm.U0, true)
        case Val.U1(l) => (Tm.U1(l), true)
        case Val.RelT => (Tm.RelT, true)
        case Val.PropT => (Tm.PropT, true)
        case Val.Rigid(Head.Glob(c), sp) if stableHead(c, sp.length) && sp.forall(_.isInstanceOf[Elim.EApp]) =>
          var ok = true
          val t = sp.reverse.foldLeft(Tm.Global(c): Tm) {
            case (acc, Elim.EApp(a, i)) =>
              val (ta, s) = quoteKeyAt(a, d)
              ok &&= s
              Tm.App(acc, ta, i)
            case (acc, _) => acc
          }
          (t, ok)
        case Val.Obj(f, as) =>
          val qs = as.map(quoteKeyAt(_, d))
          (Tm.Obj(f, qs.map(_._1)), qs.forall(_._2))
        case Val.Quote(u) =>
          val (tu, s) = quoteKeyAt(u, d)
          (Tm.Quote(tu), s)
        case Val.Rec(fs) =>
          val qs = fs.map((l, x) => (l, quoteKeyAt(x, d)))
          (Tm.Rec(qs.map((l, q) => (l, q._1))), qs.forall(_._2._2))
        case other => (quote(0, other), false)
      if stable then readBack.put(v, t)
      (t, stable)

  /** The hash-consed id of a term: equal for equal terms. */
  private def termId(t: Tm): Int = termIdAt(t, 0)

  private def termIdAt(t: Tm, depth: Int): Int =
    val cached = termIds.get(t)
    if cached != null then cached
    else if depth > Deep then termIdDeep(t)
    else
      val d = depth + 1
      // the case and the fields, with every subterm replaced by its id: equal exactly when the terms are
      // (the frequent cases of data without the generic traversal of their fields)
      def shape(x: Any): Any = x match
        case u: Tm => TermId(termIdAt(u, d))
        case xs: List[?] => xs.map(shape)
        case (a, b) => (shape(a), shape(b))
        case other => other
      val node: Any = t match
        case Tm.App(f, a, i) => AppNode(termIdAt(f, d), termIdAt(a, d), i)
        case Tm.Global(id) => GlobalNode(id)
        case Tm.Lit(l, st) => LitNode(l, st)
        case Tm.Quote(a) => QuoteNode(termIdAt(a, d))
        case Tm.Obj(f, as) => ObjNode(f, as.map(termIdAt(_, d)))
        case _ => (t.ordinal, t.productIterator.map(shape).toList)
      val id = nodeIds.getOrElseUpdate(node, nodeIds.size)
      termIds.put(t, id)
      id

  /** Whether a normal form is closed: no variables, no metas, no functions (as [[closedKey]]
   *  requires), cached per id. */
  private def closedId(t: Tm): Boolean = closedIdAt(t, 0)

  private def closedIdAt(t: Tm, depth: Int): Boolean =
    val id = termId(t)
    closedTerms.get(id) match
      case Some(b) => b
      case None if depth > Deep => closedIdDeep(t)
      case None =>
        val d = depth + 1
        val b = t match
          case Tm.Global(_) | Tm.Lit(_, _) | Tm.Base(_, _) | Tm.U0 | Tm.U1(_) | Tm.RelT | Tm.PropT => true
          case Tm.App(f, a, _) => closedIdAt(f, d) && closedIdAt(a, d)
          case Tm.Rec(fs) => fs.forall(f => closedIdAt(f._2, d))
          case Tm.Quote(a) => closedObjectAt(a, 0)
          case Tm.Obj(ObjForm.Loc(_), List(a)) => closedIdAt(a, d)
          case Tm.Arith(_, a, b, _) => closedIdAt(a, d) && closedIdAt(b, d)
          case _ => false
        closedTerms(id) = b
        b

  /** Closed object code (no variables or metas), cached per id. */
  private def closedObjectAt(t: Tm, depth: Int): Boolean =
    val id = termId(t)
    closedObjects.get(id) match
      case Some(b) => b
      case None if depth > Deep => closedObjectDeep(t)
      case None =>
        val d = depth + 1
        val b = t match
          case Tm.Var(_) | Tm.Meta(_) | Tm.AppPruning(_, _) | Tm.Lam(_, _, _) | Tm.Splice(_) => false
          case Tm.App(f, a, _) => closedObjectAt(f, d) && closedObjectAt(a, d)
          case Tm.Arith(_, a, b, _) => closedObjectAt(a, d) && closedObjectAt(b, d)
          case Tm.Obj(_, as) => as.forall(closedObjectAt(_, d))
          case Tm.Negate(a, _) => closedObjectAt(a, d)
          case Tm.Proj(a, _) => closedObjectAt(a, d)
          case _ => true
        closedObjects(id) = b
        b

  /** Runs `visit` on `root` and every node below it (children first, left to right) that is not `done`
   *  yet, with an explicit stack instead of a recursion. After `visit(x)`, `done(x)` must hold. */
  private def bottomUp[A <: AnyRef](root: A)(children: A => List[A], done: A => Boolean)(visit: A => Unit): Unit =
    if !done(root) then
      val stack = mutable.ArrayBuffer[(A, Boolean)]((root, false))
      while stack.nonEmpty do
        val (x, expanded) = stack.remove(stack.length - 1)
        if !done(x) then
          if expanded then visit(x)
          else
            stack += ((x, true))
            children(x).reverseIterator.foreach(c => if !done(c) then stack += ((c, false)))

  /** [[quoteKey]] with an explicit stack ([[bottomUp]]), for values deeper than [[Deep]]. */
  private def quoteKeyDeep(root: Val): (Tm, Boolean) =
    val cached = readBack.get(root)
    if cached != null then (cached, true)
    else
      // the results for values that are not stable data (not cached in `readBack`), for this call only
      val local = java.util.IdentityHashMap[Val, (Tm, Boolean)]()
      def result(v: Val): (Tm, Boolean) =
        val c = readBack.get(v)
        if c != null then (c, true) else local.get(v)
      def stableApp(v: Val): Boolean = v match
        case Val.Rigid(Head.Glob(c), sp) => stableHead(c, sp.length) && sp.forall(_.isInstanceOf[Elim.EApp])
        case _ => false
      def children(v: Val): List[Val] = v match
        case Val.Rigid(_, sp) if stableApp(v) => sp.reverse.collect { case Elim.EApp(a, _) => a }
        case Val.Obj(_, as) => as
        case Val.Quote(u) => List(u)
        case Val.Rec(fs) => fs.map(_._2)
        case _ => Nil
      bottomUp(root)(children, v => readBack.containsKey(v) || local.containsKey(v)) { v =>
        val (t, stable) = v match
          case Val.Lit(l, st) => (Tm.Lit(l, st), true)
          case Val.Base(b, st) => (Tm.Base(b, st), true)
          case Val.U0 => (Tm.U0, true)
          case Val.U1(l) => (Tm.U1(l), true)
          case Val.RelT => (Tm.RelT, true)
          case Val.PropT => (Tm.PropT, true)
          case Val.Rigid(Head.Glob(c), sp) if stableApp(v) =>
            var ok = true
            val t = sp.reverse.foldLeft(Tm.Global(c): Tm) {
              case (acc, Elim.EApp(a, i)) =>
                val (ta, s) = result(a)
                ok &&= s
                Tm.App(acc, ta, i)
              case (acc, _) => acc
            }
            (t, ok)
          case Val.Obj(f, as) =>
            val qs = as.map(result)
            (Tm.Obj(f, qs.map(_._1)), qs.forall(_._2))
          case Val.Quote(u) =>
            val (tu, s) = result(u)
            (Tm.Quote(tu), s)
          case Val.Rec(fs) =>
            val qs = fs.map((l, x) => (l, result(x)))
            (Tm.Rec(qs.map((l, q) => (l, q._1))), qs.forall(_._2._2))
          case other => (quote(0, other), false)
        if stable then readBack.put(v, t) else local.put(v, (t, false))
      }
      result(root)

  /** The subterms of `t` (in its fields, also inside lists and pairs), left to right. */
  private def subterms(t: Tm): List[Tm] = t match
    case Tm.App(f, a, _) => List(f, a)
    case Tm.Quote(a) => List(a)
    case Tm.Obj(_, as) => as
    case Tm.Global(_) | Tm.Lit(_, _) => Nil
    case _ =>
      def go(x: Any): Iterator[Tm] = x match
        case u: Tm => Iterator(u)
        case xs: List[?] => xs.iterator.flatMap(go)
        case (a, b) => go(a) ++ go(b)
        case _ => Iterator.empty
      t.productIterator.flatMap(go).toList

  /** [[termId]] with an explicit stack ([[bottomUp]]), for terms deeper than [[Deep]]. */
  private def termIdDeep(root: Tm): Int =
    bottomUp(root)(subterms, termIds.containsKey) { t =>
      // the case and the fields, with every subterm replaced by its id (computed before): equal exactly
      // when the terms are (the frequent cases of data without the generic traversal of their fields)
      def id(u: Tm): Int = termIds.get(u)
      def shape(x: Any): Any = x match
        case u: Tm => TermId(id(u))
        case xs: List[?] => xs.map(shape)
        case (a, b) => (shape(a), shape(b))
        case other => other
      val node: Any = t match
        case Tm.App(f, a, i) => AppNode(id(f), id(a), i)
        case Tm.Global(gid) => GlobalNode(gid)
        case Tm.Lit(l, st) => LitNode(l, st)
        case Tm.Quote(a) => QuoteNode(id(a))
        case Tm.Obj(f, as) => ObjNode(f, as.map(id))
        case _ => (t.ordinal, t.productIterator.map(shape).toList)
      termIds.put(t, nodeIds.getOrElseUpdate(node, nodeIds.size))
    }
    termIds.get(root)

  private val closedTerms = mutable.HashMap.empty[Int, Boolean]
  private val closedObjects = mutable.HashMap.empty[Int, Boolean]

  /** [[closedId]] with an explicit stack ([[bottomUp]]), for terms deeper than [[Deep]]. */
  private def closedIdDeep(root: Tm): Boolean =
    def children(t: Tm): List[Tm] = t match
      case Tm.App(f, a, _) => List(f, a)
      case Tm.Rec(fs) => fs.map(_._2)
      case Tm.Obj(ObjForm.Loc(_), List(a)) => List(a)
      case Tm.Arith(_, a, b, _) => List(a, b)
      case _ => Nil
    bottomUp(root)(children, t => closedTerms.contains(termId(t))) { t =>
      def closed(u: Tm): Boolean = closedTerms(termId(u))
      closedTerms(termId(t)) = t match
        case Tm.Global(_) | Tm.Lit(_, _) | Tm.Base(_, _) | Tm.U0 | Tm.U1(_) | Tm.RelT | Tm.PropT => true
        case Tm.App(f, a, _) => closed(f) && closed(a)
        case Tm.Rec(fs) => fs.forall(f => closed(f._2))
        case Tm.Quote(a) => closedObjectAt(a, 0)
        case Tm.Obj(ObjForm.Loc(_), List(a)) => closed(a)
        case Tm.Arith(_, a, b, _) => closed(a) && closed(b)
        case _ => false
    }
    closedTerms(termId(root))

  /** [[closedObject]] with an explicit stack ([[bottomUp]]), for terms deeper than [[Deep]]. */
  private def closedObjectDeep(root: Tm): Boolean =
    def children(t: Tm): List[Tm] = t match
      case Tm.App(f, a, _) => List(f, a)
      case Tm.Arith(_, a, b, _) => List(a, b)
      case Tm.Obj(_, as) => as
      case Tm.Negate(a, _) => List(a)
      case Tm.Proj(a, _) => List(a)
      case _ => Nil
    bottomUp(root)(children, t => closedObjects.contains(termId(t))) { t =>
      def closed(u: Tm): Boolean = closedObjects(termId(u))
      closedObjects(termId(t)) = t match
        case Tm.Var(_) | Tm.Meta(_) | Tm.AppPruning(_, _) | Tm.Lam(_, _, _) | Tm.Splice(_) => false
        case Tm.App(f, a, _) => closed(f) && closed(a)
        case Tm.Arith(_, a, b, _) => closed(a) && closed(b)
        case Tm.Obj(_, as) => as.forall(closed)
        case Tm.Negate(a, _) => closed(a)
        case Tm.Proj(a, _) => closed(a)
        case _ => true
    }
    closedObjects(termId(root))

/** A subterm in the shape of a term (see [[MemoKeys.termId]]): distinct from every other field value. */
private final case class TermId(id: Int)

/** The shapes of the most frequent terms of keys (see [[MemoKeys.termId]]); each its own class, so they
 *  are never equal to the generic shapes. */
private final case class AppNode(f: Int, a: Int, i: Icit)
private final case class GlobalNode(id: Int)
private final case class LitNode(l: hugin.syntax.Literal, st: Stage)
private final case class QuoteNode(a: Int)
private final case class ObjNode(f: ObjForm, as: List[Int])
