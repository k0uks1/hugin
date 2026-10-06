package hugin.obj

import scala.collection.mutable

/** Subtyping, members, tags and meets for a monomorphic object program (Sections 5.5, 6.2). */
final class TypeOps(p: ObjProgram):
  /** Supertypes declared by edges `τ <: a`, keyed by the subtype. */
  private val edgesFrom: Map[OType, List[TypeSym]] = p.edges.toList.groupBy(_.sub).view.mapValues(_.map(_.sup)).toMap

  private def ups(t: OType): List[OType] = t match
    case OType.Fact(c, _) =>
      c.result.toList.map {
        case OType.Con(s, _) => OType.Con(s, Nil)
        case o => o
      }.flatMap(r => List(r)) ++ (if c.result.isEmpty then List(OType.RelTop) else Nil) ++
        edgesFrom.getOrElse(t, Nil).map(OType.Con(_, Nil))
    case OType.Con(s, _) =>
      s.kind match
        case TypeKind.Open => OType.RelTop :: edgesFrom.getOrElse(OType.Con(s, Nil), Nil).map(OType.Con(_, Nil))
        case TypeKind.Refinement(b) => List(b)
    case _ => Nil

  private val subCache = mutable.HashMap.empty[(OType, OType), Boolean]

  /** τ ≤ τ' (least preorder of Section 5.5). Erroneous types are compatible with everything. */
  def isSub(a: OType, b: OType): Boolean =
    if a == b || a == OType.Err || b == OType.Err then true
    else subCache.getOrElseUpdate((a, b), {
      (a, b) match
        case (OType.Union(ms), _) => ms.forall(isSub(_, b))
        case (_, OType.Union(ms)) if ms.exists(isSub(a, _)) => true
        case _ =>
          // breadth-first search upwards
          val seen = mutable.HashSet(a)
          val queue = mutable.Queue(a)
          var found = false
          while queue.nonEmpty && !found do
            val x = queue.dequeue()
            for u <- ups(x) if !found do
              if u == b then found = true
              else
                b match
                  case OType.Union(ms) if ms.contains(u) => found = true
                  case _ =>
                if seen.add(u) then queue.enqueue(u)
          found
    })

  def isRelLike(t: OType): Boolean = t match
    case OType.Err => true
    case _ => isSub(t, OType.RelTop)

  /** mem(τ) for τ ≤ rel (Definition 5.2). */
  def members(t: OType): Set[RelSym] = memCache.getOrElseUpdate(t, t match
    case OType.Fact(c, _) => Set(c)
    case OType.Union(ms) => ms.flatMap(members).toSet
    case OType.RelTop => p.rels.toSet
    case OType.Con(_, _) => p.rels.filter(c => isSub(OType.Fact(c, Nil), t)).toSet
    case _ => Set.empty
  )
  private val memCache = mutable.HashMap.empty[OType, Set[RelSym]]

  /** A type is closed if it is a fact type or a union of closed types. */
  def isClosed(t: OType): Boolean = t match
    case OType.Fact(_, _) => true
    case OType.Union(ms) => ms.forall(isClosed)
    case _ => false

  /** Base type underlying a base type or refinement. */
  def baseOf(t: OType): Option[BaseType] = t match
    case OType.Base(b) => Some(b)
    case OType.Con(s, _) =>
      s.kind match
        case TypeKind.Refinement(b) => baseOf(b)
        case _ => None
    case _ => None

  def isBaseLike(t: OType): Boolean = baseOf(t).isDefined

  /** The meet τ ⊓ τ' (Definition 6.1). */
  def meet(a: OType, b: OType): Option[OType] =
    if a == OType.Err then Some(b)
    else if b == OType.Err then Some(a)
    else if isRelLike(a) && isRelLike(b) then
      if isSub(a, b) then Some(a)
      else if isSub(b, a) then Some(b)
      else
        val ms = members(a).intersect(members(b))
        if ms.isEmpty then None
        else Some(OType.union(p.rels.filter(ms).map(r => OType.Fact(r, Nil)).toList))
    else if isBaseLike(a) && isBaseLike(b) then
      if isSub(a, b) then Some(a) else if isSub(b, a) then Some(b) else None
    else None

  /** Labels common to all members of a closed type, with their column types per member. */
  def commonLabel(t: OType, l: String): Either[List[RelSym], List[(RelSym, Int, OType)]] =
    val ms = members(t).toList.sortBy(_.id)
    val found = ms.map(c => (c, c.labelIndex(l)))
    val missing = found.collect { case (c, None) => c }
    if missing.nonEmpty then Left(missing)
    else Right(found.collect { case (c, Some(i)) => (c, i, c.cols(i).tpe) })

  /** The join ⊔ of the column types of a common label. */
  def join(ts: List[OType]): Option[OType] =
    val d = ts.distinct
    if d.length == 1 then Some(d.head)
    else if d.forall(isRelLike) then Some(OType.union(d))
    else None
