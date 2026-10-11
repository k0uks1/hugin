package hugin.core

import scala.collection.mutable

/** The stable name of a global that a program's declarations add to the core of its libraries (issue
 *  #126, PR 7; `docs/design/incrementality-2.md`, section 9.3). Global ids are positions in
 *  `Core.globals`, which a declaration added or removed before others shifts; a key names the global by
 *  what it is: its name (a hidden lifted global of a module body is `owner.name`, a derived function
 *  `T.lift`), its stage (a shared declaration declares a constant at each stage under one name), for a
 *  family instance the family and the arguments (globals in them by their keys or library ids), and the
 *  number of earlier globals with all of these equal. */
final case class GlobalKey(name: String, stage: Stage, instance: Option[(Any, Any)], ordinal: Int)

/** The keys of the globals `from` and after of `core` (those the declarations added; the globals before
 *  are the libraries', named by their ids, which are the same in every fork of the libraries' core). */
final class GlobalKeys(core: Core, from: Int):
  private val keys: Vector[GlobalKey] =
    val seen = mutable.HashMap.empty[(String, Stage, Option[(Any, Any)]), Int]
    val out = mutable.ArrayBuffer.empty[GlobalKey]
    def ref(id: Int): Any = if id < from then ("library", id) else out(id - from)
    for id <- from until core.globals.length do
      val g = core.globals(id)
      val instance = g.instanceOf.map((fam, args) => (ref(fam), args.map(canon(_, ref))))
      val n = seen.getOrElse((g.name, g.stage, instance), 0)
      seen((g.name, g.stage, instance)) = n + 1
      out += GlobalKey(g.name, g.stage, instance, n)
    out.toVector
  private lazy val ids: Map[GlobalKey, Int] = keys.zipWithIndex.map((k, i) => k -> (from + i)).toMap

  def apply(id: Int): GlobalKey = keys(id - from)

  /** The global with the key `k`, if the core has one. */
  def find(k: GlobalKey): Option[Int] = ids.get(k)

  /** A term with its globals replaced by their references, comparable across cores. */
  private def canon(x: Any, ref: Int => Any): Any = x match
    case Tm.Global(id) => ("global", ref(id))
    case Tm.Nat(fam, n) => ("nat", ref(fam), n)
    case Tm.NatAdd(fam, b, k) => ("natAdd", ref(fam), canon(b, ref), k)
    case s: Iterable[?] => s.map(canon(_, ref)).toVector
    case p: Product if p.productArity > 0 => (p.getClass, p.productIterator.map(canon(_, ref)).toVector)
    case other => other

/** How the items elaborated against one declarations' core are moved onto another (section 9.3): the
 *  libraries' globals, metas and universe levels are the same in both (they fork the same libraries'
 *  core); a global of the old declarations is the global with the same key in the new ones. An item
 *  cannot be moved, and is elaborated again, if it refers to a global of the old declarations without
 *  a key in the new ones, or to a meta or a universe level that the old declarations created (the
 *  designer's choice: such items are not reused). */
object Rebase:
  /** The globals of `oldDecls` as globals of `newDecls`, if every global of the old declarations that
   *  the move of an item reaches has a counterpart and it reaches no meta or level the old declarations
   *  created. The move reaches the item's terms (`terms`, and the globals it used, `used`), the types and
   *  solutions of the metas its fork `from` created (they are created again), and the families and
   *  arguments of the instances it created (they are instantiated again): all are checked before
   *  anything is moved, so a move never fails half-way. */
  def declarations(
      oldDecls: ElaboratedDeclarations,
      newDecls: ElaboratedDeclarations,
      from: Core,
      terms: List[Tm],
      used: Set[Int]
  ): Option[Int => Int] =
    if oldDecls.base ne newDecls.base then return None
    val lib = oldDecls.base.core
    val (libGlobals, libMetas, libLevels) = (lib.globals.length, lib.metas.length, lib.levels.count)
    val oldCore = oldDecls.core
    // the keys of each declarations' globals are computed once (and shared by all their items)
    val (oldKeys, newKeys) = (oldDecls.summary.keys, newDecls.summary.keys)
    val map = mutable.HashMap.empty[Int, Int]
    val seenMetas = mutable.HashSet.empty[Int]
    val seenGlobals = mutable.HashSet.empty[Int]
    val todo = mutable.Stack.from(terms)
    def global(id: Int): Boolean =
      if id < libGlobals || map.contains(id) then true
      else if id >= oldCore.globals.length then
        // an instance the item created: its family and arguments are moved too
        if seenGlobals.add(id) then
          from.globals(id).instanceOf match
            case Some((fam, args)) =>
              todo.pushAll(args)
              global(fam)
            case None => false
        else true
      else
        newKeys.find(oldKeys(id)) match
          case Some(n) =>
            map(id) = n
            true
          case None => false
    def meta(m: Int): Boolean =
      if m < libMetas then true
      else if m < oldCore.metas.length then false
      else
        if seenMetas.add(m) then
          val e = from.metas(m)
          todo.push(from.quote(0, e.ty))
          e.solution.foreach(v => todo.push(from.quote(0, v)))
        true
    var ok = used.forall(global)
    while ok && todo.nonEmpty do
      ok = !Tm.exists(todo.pop()) {
        case Tm.Global(id) => !global(id)
        case Tm.Nat(fam, _) => !global(fam)
        case Tm.NatAdd(fam, _, _) => !global(fam)
        case Tm.Meta(m) => !meta(m)
        case Tm.U1(l) => !l.isConst && l.v >= libLevels && l.v < oldCore.levels.count
        case _ => false
      }
    Option.when(ok)(id => if id < libGlobals then id else map(id))
