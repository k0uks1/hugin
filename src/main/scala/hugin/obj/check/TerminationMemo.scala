package hugin.obj
package check

import java.util.concurrent.atomic.AtomicLong

/** The termination verdicts of recursive components, memoised across compilations (issue #126, PR 6): an
 *  edit outside a component does not check its termination again.
 *
 *  A verdict that holds (`Finite`, `Accepted`) is a function of what the check reads: the component (its
 *  relations in order), the rules of the component, and, for every relation and type those mention, its
 *  shape (name, kind, columns with their types, result type, family instance) and the measure positions
 *  of its `%terminates` directive. The key is that structure with every relation and type symbol replaced
 *  by the index of its first occurrence (symbols are created afresh by every compilation and compare by
 *  identity), so equal keys are the same component up to renaming of symbols and positions. A value
 *  without structural equality stays as itself in the key, so it never matches another compilation's
 *  (no reuse, never a wrong verdict). Rejections are not memoised (their diagnostics carry positions),
 *  and neither are verdicts asked with explanations (their lines carry positions): the cache is consulted
 *  only without `--explain-termination`, where the lines of an accepted verdict are not read.
 *
 *  The cache is per process and bounded (least recently used entries are dropped). */
object TerminationMemo:
  private val maxEntries = 4096

  private val cache = new java.util.LinkedHashMap[Vector[Any], Verdict](256, 0.75f, true):
    override def removeEldestEntry(e: java.util.Map.Entry[Vector[Any], Verdict]): Boolean = size > maxEntries

  /** The number of verdicts computed through the memo (for tests). */
  val computed: AtomicLong = AtomicLong()

  def verdict(rc: RecursiveComponent)(compute: => Verdict): Verdict =
    val key = Key(rc).key
    cache.synchronized(Option(cache.get(key))) match
      case Some(v) => v
      case None =>
        computed.incrementAndGet()
        val v = compute
        v match
          case Verdict.Finite | _: Verdict.Accepted => cache.synchronized(cache.put(key, v))
          case _: Verdict.Rejected =>
        v

  /** A symbol by the index of its first occurrence in the key. */
  private final case class RelRef(index: Int)
  private final case class TypeRef(index: Int)

  /** A node of the structural copy: the class of a case class (or enum case with fields) and its fields. */
  private final case class Node(cls: Class[?], fields: Vector[Any])

  private final class Key(rc: RecursiveComponent):
    private val rels = scala.collection.mutable.LinkedHashMap.empty[RelSym, Int]
    private val types = scala.collection.mutable.LinkedHashMap.empty[TypeSym, Int]

    private def canon(x: Any): Any = x match
      case r: RelSym => RelRef(rels.getOrElseUpdate(r, rels.size))
      case t: TypeSym => TypeRef(types.getOrElseUpdate(t, types.size))
      case a: Array[?] => a.toVector.map(canon)
      case s: Set[?] => s.map(canon)
      case m: Map[?, ?] => m.map((k, v) => canon(k) -> canon(v))
      case s: Seq[?] => s.map(canon)
      case p: Product if p.productArity > 0 => Node(p.getClass, p.productIterator.map(canon).toVector)
      case other => other

    val key: Vector[Any] =
      val structure = Vector(canon(rc.comp), canon(rc.rules))
      // the shapes of the symbols, until no new symbol appears (a column type may mention another one)
      val relShapes = scala.collection.mutable.ArrayBuffer.empty[Any]
      val typeShapes = scala.collection.mutable.ArrayBuffer.empty[Any]
      while relShapes.length < rels.size || typeShapes.length < types.size do
        while relShapes.length < rels.size do
          val r = rels.keys.drop(relShapes.length).head
          val measure = rc.facts(r).terminates.map(_._1)
          relShapes += Vector(r.name, r.displayName, canon(r.kind), canon(r.cols), canon(r.result), canon(r.instanceOf), measure)
        while typeShapes.length < types.size do
          val t = types.keys.drop(typeShapes.length).head
          typeShapes += Vector(t.name, t.displayName, canon(t.kind), canon(t.instanceOf))
      structure ++ Vector(relShapes.toVector, typeShapes.toVector)
