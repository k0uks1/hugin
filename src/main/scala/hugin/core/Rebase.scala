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
  /** The globals of `oldDecls` as globals of `newDecls`, if every one that `terms` and `used` refer to has
   *  a counterpart and they refer to no meta or level the old declarations created. */
  def declarations(
      oldDecls: ElaboratedDeclarations,
      newDecls: ElaboratedDeclarations,
      terms: List[Tm],
      used: Set[Int]
  ): Option[Int => Int] =
    if oldDecls.base ne newDecls.base then return None
    val lib = oldDecls.base.core
    val (libGlobals, libMetas, libLevels) = (lib.globals.length, lib.metas.length, lib.levels.count)
    val (oldCore, newCore) = (oldDecls.core, newDecls.core)
    val (oldKeys, newKeys) = (GlobalKeys(oldCore, libGlobals), GlobalKeys(newCore, libGlobals))
    val map = mutable.HashMap.empty[Int, Int]
    def global(id: Int): Boolean =
      id < libGlobals || id >= oldCore.globals.length || map.contains(id) || newKeys.find(oldKeys(id)).exists { n =>
        map(id) = n
        true
      }
    val ok = used.forall(global) && terms.forall(t =>
      !Tm.exists(t) {
        case Tm.Global(id) => !global(id)
        case Tm.Meta(m) => m >= libMetas && m < oldCore.metas.length
        case Tm.U1(l) => !l.isConst && l.v >= libLevels && l.v < oldCore.levels.count
        case _ => false
      }
    )
    Option.when(ok)(id => if id < libGlobals then id else map(id))
