package hugin.meta

import hugin.util.*
import hugin.syntax.*
import hugin.obj.BaseType
import scala.collection.mutable

enum SymKind:
  /** `a : type.` or `a : type <: b.` (possibly a family). */
  case ObjType

  /** `a : type = { l : t, ... }.` — a relation whose fact type is `a`. */
  case Struct

  /** `c : τ̄ -> rel.` */
  case Rel

  /** `c : τ̄ -> a.` with `a` open. */
  case Ctor

  /** `n : type = τ.` / `%abbrev`. */
  case TypeDef

  /** `f : τ̄ -> prop` with clauses or a definition. */
  case FormulaFn

  /** Any other meta definition (constants, signatures, modules, functors). */
  case MetaDef

  /** Parameters of meta functions and lambdas (including implicit type parameters). */
  case MetaParam

  /** `n : type = %builtin b.`: a base type (`int`, `float`, `string`), declared by the prelude. */
  case BaseType

  def isObjectDecl: Boolean = this match
    case ObjType | Struct | Rel | Ctor => true
    case _ => false

  def describe: String = this match
    case ObjType => "object type"
    case Struct => "struct"
    case Rel => "relation"
    case Ctor => "constructor"
    case TypeDef => "type definition"
    case FormulaFn => "formula function"
    case MetaDef => "meta definition"
    case MetaParam => "meta parameter"
    case BaseType => "base type"

/** A declared name (meta-level symbol): an identity with what the namer knows about it. What the typer
 *  computes about a symbol is in its [[SymTable]] (`CompilationUnit.symbols`).
 *
 *  Symbols are equal if their keys are: a key is stable across re-elaboration (see [[SymKey]]), and no
 *  two symbols of one compilation share a key (checked by [[SymKeys]] when a symbol is created).
 *
 *  @param key     the stable identity of the symbol
 *  @param item    the key of the declaring item, for declarations entered by the namer
 *  @param decl    the declaring item, for declarations entered by the namer
 *  @param clauses the clauses of a formula function, in source order
 *  @param abbrev  whether a type definition is marked `%abbrev` (always expanded)
 *  @param base    the base type of a `BaseType` symbol
 */
final class Sym private (
    val name: String,
    val kind: SymKind,
    val span: Span,
    val owner: Scope,
    val key: SymKey,
    val item: Option[ItemKey],
    val decl: Option[Item],
    val clauses: List[Rule],
    val abbrev: Boolean,
    val base: Option[BaseType]
):
  override def equals(that: Any): Boolean = that match
    case s: Sym => (this eq s) || key == s.key
    case _ => false
  override val hashCode: Int = key.hashCode
  override def toString: String = name

object Sym:
  /** Creates a symbol with a key that no other symbol of the compilation has (registered in `keys`). */
  def apply(
      name: String,
      kind: SymKind,
      span: Span,
      owner: Scope,
      key: SymKey,
      keys: SymKeys,
      item: Option[ItemKey] = None,
      decl: Option[Item] = None,
      clauses: List[Rule] = Nil,
      abbrev: Boolean = false,
      base: Option[BaseType] = None
  ): Sym =
    keys.register(key)
    new Sym(name, kind, span, owner, key, item, decl, clauses, abbrev, base)

/** A lexical scope: program, module body, meta function parameters, lambda.
 *
 *  @param key the stable identity of the scope; the symbols bound in it have keys `SymKey(key, name)`
 */
final class Scope(val parent: Option[Scope], val description: String, val key: ScopeKey):
  val decls: mutable.LinkedHashMap[String, Sym] = mutable.LinkedHashMap.empty

  /** Names for which a key `SymKey(key, name)` was handed out (see [[claim]]). */
  private val claimed = mutable.HashSet.empty[String]

  private var frozen = false

  /** Forbids entering further names (the scope of a library, shared by the compilations importing it). */
  def freeze(): Unit = frozen = true

  private def check(name: String): Unit =
    if frozen then throw IllegalStateException(s"`$name` entered into the frozen scope $key")

  /** Whether the key `SymKey(key, name)` is still free; claims it if so. A binder that shadows another
   *  one in the same scope (a duplicate label in a function type, a lambda parameter named like one of
   *  its implicit parameters) finds the key taken and is given a key in a scope of its own. */
  def claim(name: String): Boolean =
    check(name)
    claimed.add(name)

  /** Told about every lookup in this scope, while set (see [[observing]]). */
  private var observer: Scope.Observer | Null = null

  /** Runs `body`, telling `o` about every lookup in this scope (also through a nested scope): the names
   *  looked up, found or not, the symbols found, and whether all names were listed. The per-item
   *  elaboration of a program records with it which names and declarations an item uses (see
   *  `hugin.compiler.ProgramElab`); the scope itself does not change. */
  def observing[T](o: Scope.Observer)(body: => T): T =
    val saved = observer
    observer = o
    try body
    finally observer = saved

  def lookupLocal(name: String): Option[Sym] =
    val found = decls.get(name)
    val o = observer
    if o != null then
      o.looked(name)
      found.foreach(o.found)
    found

  def lookup(name: String): Option[Sym] =
    lookupLocal(name).orElse(parent.flatMap(_.lookup(name)))

  def allNames: Iterator[String] =
    val o = observer
    if o != null then o.listed()
    decls.keysIterator ++ parent.iterator.flatMap(_.allNames)

  def enter(s: Sym): Unit =
    check(s.name)
    decls(s.name) = s

object Scope:
  /** Told about the lookups in a scope (see [[Scope.observing]]). */
  trait Observer:
    /** A name was looked up in the scope (whether or not it is declared there). */
    def looked(name: String): Unit

    /** A lookup found this symbol in the scope. */
    def found(s: Sym): Unit

    /** All names of the scope were listed (e.g. for a suggestion of a similar name). */
    def listed(): Unit
