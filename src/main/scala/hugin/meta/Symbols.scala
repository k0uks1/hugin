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

/** A declared name (meta-level symbol). */
final class Sym(val name: String, val kind: SymKind, val span: Span, val owner: Scope):
  val id: Int = Sym.next()

  /** Declaring item (if any). */
  var decl: Option[Item] = None

  /** Clauses of a formula function. */
  val clauses: mutable.ListBuffer[Rule] = mutable.ListBuffer.empty

  var abbrev: Boolean = false

  /** The base type of a `BaseType` symbol. */
  var base: Option[BaseType] = None

  /** Labels and column count for object relations (filled by the typer). */
  var used: Boolean = false

  /** `%mode` declarations of a formula function (Section 4.8). */
  var fnModes: List[(List[Boolean], Span)] = Nil
  override def toString: String = name

object Sym:
  private var n = 0
  private def next(): Int = { n += 1; n }

/** A lexical scope: program, module body, meta function parameters, lambda. */
final class Scope(val parent: Option[Scope], val description: String):
  val decls: mutable.LinkedHashMap[String, Sym] = mutable.LinkedHashMap.empty

  /** For the scopes of files (the program, the prelude, imported files): the prefix of the names of their
   *  object declarations (`""` for none). Module bodies inside files get a fresh prefix instead. */
  var qualifier: Option[String] = None

  /** Names whose object declarations get the prefix `prelude.` because the program declares the same name. */
  var shadowed: Set[String] = Set.empty

  def lookupLocal(name: String): Option[Sym] = decls.get(name)

  def lookup(name: String): Option[Sym] =
    decls.get(name).orElse(parent.flatMap(_.lookup(name)))

  def allNames: Iterator[String] = decls.keysIterator ++ parent.iterator.flatMap(_.allNames)

  def enter(s: Sym): Unit = decls(s.name) = s
