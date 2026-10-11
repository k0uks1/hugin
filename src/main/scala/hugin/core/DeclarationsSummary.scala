package hugin.core

import hugin.util.Span
import scala.collection.mutable

/** The fingerprint of a global of a program's declarations (issue #126, PR 7 step 3; section 9.4 of
 *  `docs/design/incrementality-2.md`). As in GHC's interfaces, it covers the global's entry (name,
 *  stage, type, kind with its body: a definition's value, a function's case tree and clauses, the
 *  constructors of an inductive family; spans; family instance; shared counterpart) with every other
 *  global of the declarations replaced by its fingerprint, so that a change propagates along the
 *  references (a definition an item can unfold, transitively); the globals of a component of
 *  references are fingerprinted together. `hash` covers the data (128 bits); `exact` holds what is
 *  compared exactly, not hashed: the spans (positions resolve through their sources) and the values
 *  without structural equality, compared by identity (so a fingerprint with one never matches another
 *  core's: a miss, never a wrong reuse). */
final case class Fingerprint(hash: (Long, Long), exact: Vector[Any])

/** A value compared by identity (it has no structural equality across cores). */
final class Opaque(val value: Any):
  override def equals(that: Any): Boolean = that match
    case o: Opaque => o.value.asInstanceOf[AnyRef] eq value.asInstanceOf[AnyRef]
    case _ => false
  override def hashCode: Int = System.identityHashCode(value)

/** What an object item can read of a program's declarations, comparable across their elaborations: the
 *  fingerprint of each global by key, the outcome of each name in each per-name table, and each whole
 *  table, with globals named by their keys ([[GlobalKey]]) and the libraries' globals by their ids. */
final class DeclarationsSummary(decls: ElaboratedDeclarations):
  private val core = decls.core
  private val libraries = decls.base.core.globals.length
  val keys: GlobalKeys = GlobalKeys(core, libraries)
  private def key(id: Int): Any = if id < libraries then ("library", id) else keys(id)

  /** The fingerprint of the global with the key `k`, if the declarations have one. */
  def fingerprint(k: GlobalKey): Option[Fingerprint] = keys.find(k).map(id => fingerprints(id - libraries))

  private lazy val fingerprints: Vector[Fingerprint] =
    val ids = libraries until core.globals.length
    val deps = ids.map { id =>
      val refs = mutable.LinkedHashSet.empty[Int]
      Canonical(r => { if r >= libraries then refs += r; r }).entry(core.globals(id))
      refs.toList.filter(_ != id)
    }
    val out = new Array[Fingerprint | Null](ids.length)
    for component <- hugin.util.Graphs.components(ids, id => deps(id - libraries)) do
      val inside = component.toSet
      val canon = Canonical(r =>
        if r < libraries then ("library", r)
        else if inside(r) then ("group", keys(r))
        else ("fingerprint", out(r - libraries).nn)
      )
      val group = component.sortBy(keys(_).toString).map(id => (keys(id), canon.entry(core.globals(id))))
      val (hash, exact) = Hashing.of(group)
      for id <- component do out(id - libraries) = Fingerprint(Hashing.combine(hash, keys(id)), exact)
    out.toVector.map(_.nn)

  /** The outcome of the name `n` in the per-name table `channel`. */
  def name(channel: String, n: String): Any =
    val state = decls.elaborator.state
    channel match
      case "scope" => state.scope.snapshot.get(n).map(key)
      case "erroneous" => state.erroneous.unobserved(n)
      case "unelaborated" => state.unelaborated.unobserved(n)
      case "functionNames" => state.functionNames.unobserved(n)
      case "declaredHere" => state.declaredHere.unobserved(n)
      case other => Opaque(other) // an unknown table: never equal

  /** The whole table `channel`, comparable (`None` for a table an item may not depend on as a whole:
   *  the globals, metas and levels, which make an item depend on all of the declarations). */
  def table(channel: String): Option[Any] = tables.getOrElseUpdate(channel, computeTable(channel))

  // the tables canonicalized once per declarations (every item that reads one whole compares it)
  private val tables = mutable.HashMap.empty[String, Option[Any]]

  private def computeTable(channel: String): Option[Any] =
    val state = decls.elaborator.state
    val canon = Canonical(key)
    lazy val (bodyIds, anonymous, prefixes, fileRanks, memo) = core.moduleTables
    lazy val (opened, exported, signatures, droppedUses) = state.tables
    channel match
      case "scope" => Some(state.scope.snapshot.toVector.map((n, id) => (n, key(id))))
      case "erroneous" => Some(state.erroneous.unobserved)
      case "unelaborated" => Some(state.unelaborated.unobserved)
      case "functionNames" => Some(state.functionNames.unobserved)
      case "declaredHere" => Some(state.declaredHere.unobserved)
      case "opened" => Some(opened.toVector.map((n, ds) => (n, ds.map((id, sp) => (key(id), sp)))))
      case "exported" => Some(exported.map((sp, m) => (sp, canon.value(m))))
      case "signatures" => Some(signatures)
      case "droppedUses" => Some(droppedUses)
      case "instances" => Some(core.familyTable.map { case ((fam, args), id) => (key(fam), args.map(canon.tm), key(id)) })
      case "derived" => Some(core.derivedTable.map { case ((id, label), d) => (key(id), label, key(d)) })
      case "objEdges" => Some(core.edgesTable.map((sub, sup) => (canon.tm(core.quote(0, sub)), key(sup))))
      case "hygiene" => Some(core.hygieneCount)
      case "bodyIds" => Some(bodyIds)
      case "prefixes" => Some((anonymous, prefixes))
      case "fileRanks" => Some(fileRanks)
      case "moduleMemo" => Some(Opaque(memo)) // instances of module bodies: by identity
      case _ => None

/** A structural copy of the entries and terms of a core with every global replaced by `ref(id)`. A
 *  value of an unknown kind stays as itself, compared by identity ([[Opaque]]). */
private final class Canonical(ref: Int => Any):
  def entry(g: GlobalEntry): Any =
    Vector(
      g.name,
      g.stage,
      g.pending,
      g.hidden,
      g.inCycle,
      g.axiom,
      g.parameters,
      g.span,
      g.declSpan,
      g.placedAt,
      tm(g.tyTm),
      kind(g.kind),
      g.instanceOf.map((fam, args) => (ref(fam), args.map(tm))),
      g.shared.map(s => (s.side, ref(s.counterpart), if s.lift >= 0 then ref(s.lift) else -1, if s.reify >= 0 then ref(s.reify) else -1))
    )

  def kind(k: GlobalKind): Any = k match
    case GlobalKind.Postulate | GlobalKind.Symbols => k
    case GlobalKind.Object(d) => ("object", objDecl(d))
    case GlobalKind.Family(d, arity) => ("family", objDecl(d), arity)
    case GlobalKind.Definition(t, _) => ("definition", tm(t))
    case GlobalKind.Inductive(ctors) => ("inductive", ctors.map(ref))
    case GlobalKind.Constructor(family) => ("constructor", ref(family))
    case GlobalKind.Function(arity, body) =>
      ("function", arity, body.map(b => (tree(b.tree), b.clauses.map(c => (c.body.map(tm), c.names, c.patterns.map(tm))))))
    case GlobalKind.Primitive(op, ctors) => ("primitive", op, ctors.map(ref))
    case GlobalKind.Opaque(t, f) => ("opaque", t.map(tm), f.map((a, b) => kind(GlobalKind.Function(a, Some(b)))))

  private def objDecl(d: ObjDecl): Any = d match
    case ObjDecl.Refinement(base) => ("refinement", tm(base))
    case other => other

  private def tree(t: CaseTree): Any = t match
    case CaseTree.Leaf(body, size, subst, clause) => ("leaf", tm(body), size, subst.map(tm), clause)
    case CaseTree.Split(level, branches) => ("split", level, branches.map(b => (ref(b.ctor), b.arity, tree(b.tree))))
    case CaseTree.SplitAtom(level, branches, default) => ("atom", level, branches.map((v, t) => (tm(v), tree(t))), tree(default))
    case CaseTree.SplitNat(level, fam, values, offset, above, below) =>
      ("nat", level, ref(fam), values.map((n, t) => (n, tree(t))), offset, tree(above), tree(below))

  def tm(t: Tm): Any = t match
    case Tm.Global(id) => ("global", ref(id))
    case Tm.Nat(fam, n) => ("nat", ref(fam), n)
    case Tm.NatAdd(fam, b, k) => ("natAdd", ref(fam), tm(b), k)
    case Tm.Meta(m) => ("meta", m)
    case _: Tm.Module | _: Tm.Trace => Opaque(t)
    case p => (p.getClass, p.productIterator.map(value).toVector)

  def value(x: Any): Any = x match
    case t: Tm => tm(t)
    case _: (String | Int | Long | Boolean | Double | BigInt | Span | Level) => x
    case o: Option[?] => o.map(value)
    case s: Set[?] => s.map(value)
    case l: Iterable[?] => l.map(value).toVector
    case p: Product if p.productArity == 0 => p
    case p: (Tuple | hugin.syntax.Literal | Icit | Stage | hugin.obj.BaseType | hugin.obj.ArithOp | SigReq | ObjForm | elab.ImportedModule) =>
      (p.getClass, p.asInstanceOf[Product].productIterator.map(value).toVector)
    case other => Opaque(other)

/** A 128-bit hash of the data of a canonical value, and the parts compared exactly (spans, opaque values). */
private object Hashing:
  def of(x: Any): ((Long, Long), Vector[Any]) =
    var a = 0x9e3779b97f4a7c15L
    var b = 0xc2b2ae3d27d4eb4fL
    val exact = mutable.ArrayBuffer.empty[Any]
    def mix(v: Long): Unit =
      a = splitmix(a ^ v)
      b = splitmix(b + v * 0x9e3779b97f4a7c15L)
    def go(x: Any): Unit = x match
      case s: String =>
        mix(1); mix(s.length.toLong); s.foreach(c => mix(c.toLong))
      case i: Int => mix(2); mix(i.toLong)
      case l: Long => mix(3); mix(l)
      case z: Boolean => mix(4); mix(if z then 1 else 0)
      case d: Double => mix(5); mix(java.lang.Double.doubleToLongBits(d))
      case n: BigInt => mix(16); go(n.toString(16))
      case f: Fingerprint => mix(6); mix(f.hash._1); mix(f.hash._2); exact ++= f.exact
      case c: Class[?] => mix(7); go(c.getName)
      case v: Vector[?] => mix(8); mix(v.length.toLong); v.foreach(go)
      case l: List[?] => mix(8); mix(l.length.toLong); l.foreach(go)
      case s: Set[?] => mix(9); go(s.toVector.map(e => of(e)).sortBy(_._1))
      case o: Option[?] => mix(10); o.foreach(go)
      case k: GlobalKey => mix(11); go(k.name); go(k.stage.toString); go(k.instance); mix(k.ordinal.toLong)
      case t: Tuple => mix(12); t.productIterator.foreach(go)
      case p: Product if p.productArity == 0 => mix(13); go(p.getClass.getName); go(p.productPrefix)
      case p: Product if !p.isInstanceOf[Span] && !p.isInstanceOf[Level] => mix(14); go(p.getClass.getName); p.productIterator.foreach(go)
      case other =>
        mix(15)
        exact += other
    go(x)
    ((a, b), exact.toVector)

  def combine(h: (Long, Long), k: GlobalKey): (Long, Long) =
    val (k1, _) = of(k)
    (splitmix(h._1 ^ k1._1), splitmix(h._2 + k1._2))

  private def splitmix(x0: Long): Long =
    var z = x0 + 0x9e3779b97f4a7c15L
    z = (z ^ (z >>> 30)) * 0xbf58476d1ce4e5b9L
    z = (z ^ (z >>> 27)) * 0x94d049bb133111ebL
    z ^ (z >>> 31)
