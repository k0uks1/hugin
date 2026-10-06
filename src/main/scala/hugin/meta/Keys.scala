package hugin.meta

import hugin.syntax.Trees.*
import hugin.util.Span
import scala.collection.mutable
import scala.util.hashing.MurmurHash3

/** Stable identities of scopes, items and symbols (step 6 of `docs/INCREMENTALITY.md`). A key depends only
 *  on the names and the span-insensitive structure of the source, never on positions, item indices or the
 *  order in which the typer happens to elaborate items, so it survives re-elaboration after an edit that
 *  does not touch the item (inserting a blank line or an unrelated item before it, for example). */
enum ScopeKey:
  /** The top-level scope of a source file (the program, an imported file or the prelude). */
  case File(path: String)

  /** The scope of the `n`-th module body `{ ... }` in the item `owner` (counted with the item's other
   *  local scopes, in elaboration order). */
  case Module(owner: ItemKey, n: Int)

  /** The parameters of a meta definition, formula function or type definition. */
  case Params(owner: SymKey)

  /** The `n`-th local scope of the item `owner` (a lambda, the fields of a record or signature, the
   *  parameters of clauses, an instantiation of implicit parameters), counted in elaboration order. */
  case Local(owner: ItemKey, n: Int)

  /** The path of the source file the scope belongs to. */
  def file: String = this match
    case File(path) => path
    case Module(owner, _) => owner.scope.file
    case Params(owner) => owner.scope.file
    case Local(owner, _) => owner.scope.file

/** The identity of an item within its scope. */
enum ItemId:
  /** A declaration or definition of `name`; `dup` counts the earlier items of the same name in the scope
   *  (non-zero only for redeclarations, E0102). */
  case Named(name: String, dup: Int)

  /** A rule named `@name`; `dup` counts the earlier rules of that name in the scope. */
  case Rule(name: String, dup: Int)

  /** An anonymous item (a rule, query, directive or subtyping edge) identified by its kind and the
   *  span-insensitive hash of its tree; `occurrence` counts the earlier items in the scope with the same
   *  kind and hash (identical items, or hash collisions). */
  case Anon(kind: String, hash: Int, occurrence: Int)

/** The identity of an item: its scope and its identity there. */
final case class ItemKey(scope: ScopeKey, id: ItemId)

object ItemKey:
  /** The keys of the items of one scope, in item order. Inserting, removing or editing an item changes
   *  only its own key and the keys of later items with the same name, or the same kind and hash. */
  def assign(scope: ScopeKey, items: List[Item]): List[ItemKey] =
    val named = mutable.HashMap.empty[String, Int]
    val rules = mutable.HashMap.empty[String, Int]
    val anons = mutable.HashMap.empty[(String, Int), Int]
    def next[K](m: mutable.HashMap[K, Int], k: K): Int =
      val n = m.getOrElse(k, 0)
      m(k) = n + 1
      n
    def anon(kind: String, item: Item): ItemId =
      val h = structuralHash(item)
      ItemId.Anon(kind, h, next(anons, (kind, h)))
    items.map { item =>
      val id = item match
        case d: Decl => ItemId.Named(d.name.name, next(named, d.name.name))
        case d: Def => ItemId.Named(d.name.name, next(named, d.name.name))
        case hugin.syntax.Trees.Rule(Some(n), _, _) => ItemId.Rule(n.name, next(rules, n.name))
        case r: hugin.syntax.Trees.Rule => anon("rule", r)
        case q: Query => anon("query", q)
        case d: Directive => anon("directive", d)
        case e: SubEdge => anon("edge", e)
      ItemKey(scope, id)
    }

  /** A hash of a surface tree that ignores positions: spans are skipped wherever they occur (surface trees
   *  keep most spans in a second parameter list, which `hashCode` already ignores, but some nodes carry a
   *  span as a field). Deterministic across runs. */
  def structuralHash(x: Any): Int = x match
    case _: Span => 0
    case p: Product if p.productArity > 0 =>
      var h = MurmurHash3.mix(MurmurHash3.productSeed, p.productPrefix.hashCode)
      p.productIterator.foreach(e => h = MurmurHash3.mix(h, structuralHash(e)))
      MurmurHash3.finalizeHash(h, p.productArity)
    case other => other.toString.hashCode

/** The identity of a symbol: the scope it is bound in and its name. No two symbols of a compilation have
 *  the same key (see [[SymKeys]]). */
final case class SymKey(scope: ScopeKey, name: String):
  override def toString: String = s"$scope.$name"

/** The keys of the symbols created in one compilation, to check that keys are unique. The keys of the
 *  libraries a compilation uses were registered when the libraries were named and elaborated (once, see
 *  [[hugin.compiler.ElaboratedLibrary]]); they are inherited, not registered again. */
final class SymKeys:
  private val seen = mutable.HashSet.empty[SymKey]
  private val inherited = mutable.ArrayBuffer.empty[SymKeys]

  /** Adds the keys of a library (they must not be registered again). */
  def inherit(keys: SymKeys): Unit = if !inherited.exists(_ eq keys) then inherited += keys

  /** Adds the keys registered in `keys` (they must be new here) and inherits what it inherited: the
   *  per-item registries of a program are merged into the registry of the whole program. */
  def absorb(keys: SymKeys): Unit =
    for k <- keys.seen do register(k)
    keys.inherited.foreach(inherit)

  /** Whether a key was registered here or in an inherited registry. */
  def contains(key: SymKey): Boolean = seen.contains(key) || inherited.exists(_.contains(key))

  /** Records a new key; fails if a symbol with this key was created before. */
  def register(key: SymKey): Unit =
    assert(!inherited.exists(_.contains(key)) && seen.add(key), s"two symbols with the key $key")

  /** The keys registered so far, also those inherited. */
  def all: Set[SymKey] = seen.toSet ++ inherited.flatMap(_.all)
