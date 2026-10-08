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
 *    stable data, object code over stable data, and records and quotes of it. No forcing is involved in reading them back (no metas, whose solutions may
 *    be undone, no function or definition that a later declaration may make reduce), so the cached term
 *    is exactly what `quote(0, v)` gives at any time. Any other value is read back with `quote` as
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
  private val nodeIds = mutable.HashMap.empty[(Int, List[Any]), Int]
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

  /** `quote(0, v)`, and whether `v` is stable data (then it is cached for `v`). */
  private def quoteKey(v: Val): (Tm, Boolean) =
    val cached = readBack.get(v)
    if cached != null then (cached, true)
    else
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
              val (ta, s) = quoteKey(a)
              ok &&= s
              Tm.App(acc, ta, i)
            case (acc, _) => acc
          }
          (t, ok)
        case Val.Obj(f, as) =>
          val qs = as.map(quoteKey)
          (Tm.Obj(f, qs.map(_._1)), qs.forall(_._2))
        case Val.Quote(u) =>
          val (tu, s) = quoteKey(u)
          (Tm.Quote(tu), s)
        case Val.Rec(fs) =>
          val qs = fs.map((l, x) => (l, quoteKey(x)))
          (Tm.Rec(qs.map((l, q) => (l, q._1))), qs.forall(_._2._2))
        case other => (quote(0, other), false)
      if stable then readBack.put(v, t)
      (t, stable)

  /** The hash-consed id of a term: equal for equal terms. */
  private def termId(t: Tm): Int =
    val cached = termIds.get(t)
    if cached != null then cached
    else
      // the case and the fields, with every subterm replaced by its id: equal exactly when the terms are
      def shape(x: Any): Any = x match
        case u: Tm => TermId(termId(u))
        case xs: List[?] => xs.map(shape)
        case (a, b) => (shape(a), shape(b))
        case other => other
      val id = nodeIds.getOrElseUpdate((t.ordinal, t.productIterator.map(shape).toList), nodeIds.size)
      termIds.put(t, id)
      id

  private val closedTerms = mutable.HashMap.empty[Int, Boolean]
  private val closedObjects = mutable.HashMap.empty[Int, Boolean]

  /** Whether a normal form is closed: no variables, no metas, no functions (as [[closedKey]]
   *  requires), cached per id. */
  private def closedId(t: Tm): Boolean = closedTerms.getOrElseUpdate(
    termId(t),
    t match
      case Tm.Global(_) | Tm.Lit(_, _) | Tm.Base(_, _) | Tm.U0 | Tm.U1(_) | Tm.RelT | Tm.PropT => true
      case Tm.App(f, a, _) => closedId(f) && closedId(a)
      case Tm.Rec(fs) => fs.forall(f => closedId(f._2))
      case Tm.Quote(a) => closedObject(a)
      case Tm.Obj(ObjForm.Loc(_), List(a)) => closedId(a)
      case Tm.Arith(_, a, b, _) => closedId(a) && closedId(b)
      case _ => false
  )

  /** Closed object code (no variables or metas), cached per id. */
  private def closedObject(t: Tm): Boolean = closedObjects.getOrElseUpdate(
    termId(t),
    t match
      case Tm.Var(_) | Tm.Meta(_) | Tm.AppPruning(_, _) | Tm.Lam(_, _, _) | Tm.Splice(_) => false
      case Tm.App(f, a, _) => closedObject(f) && closedObject(a)
      case Tm.Arith(_, a, b, _) => closedObject(a) && closedObject(b)
      case Tm.Obj(_, as) => as.forall(closedObject)
      case Tm.Negate(a, _) => closedObject(a)
      case Tm.Proj(a, _) => closedObject(a)
      case _ => true
  )

/** A subterm in the shape of a term (see [[MemoKeys.termId]]): distinct from every other field value. */
private final case class TermId(id: Int)
