package hugin.meta

import hugin.util.*
import hugin.syntax.*
import hugin.obj.{TParam, BaseType}
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
  /** Base types of the prelude (`int`, `float`, `string`). */
  case PreludeType

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
    case PreludeType => "base type"

/** A declared name (meta-level symbol). */
final class Sym(val name: String, var kind: SymKind, val span: Span, val owner: Scope):
  val id: Int = Sym.next()
  /** Declaring item (if any). */
  var decl: Option[Item] = None
  /** Clauses of a formula function. */
  val clauses: mutable.ListBuffer[Rule] = mutable.ListBuffer.empty
  /** Position in the scope's item order (for the forward-reference check). */
  var order: Int = 0
  /** Meta type, filled by the typer. */
  var mtype: MType | Null = null
  /** Static normal form (for transparent definitions: types, records of types and relations). */
  var static: Option[MExpr] = None
  /** For signature definitions (`graph : mod = {...}`): the signature itself. */
  var sigValue: Option[MType] = None
  /** Typing state for lazily elaborated symbols. */
  var state: Sym.State = Sym.State.Pending
  /** Family type parameters (object declarations) or type definition parameters. */
  var tparams: List[TParam] = Nil
  /** Type definition parameters as meta parameters, and the elaborated right-hand side. */
  var typeDefParams: List[Sym] = Nil
  var typeDefRhs: Option[hugin.obj.OType] = None
  var abbrev: Boolean = false
  /** Number of explicit parameters (for formula functions: arity). */
  var arity: Int = 0
  /** Base type for prelude symbols. */
  var base: Option[BaseType] = None
  /** Labels and column count for object relations (filled by the typer). */
  var used: Boolean = false
  override def toString: String = name

object Sym:
  enum State:
    case Pending, InProgress, Done
  private var n = 0
  private def next(): Int = { n += 1; n }

/** A lexical scope: program, module body, meta function parameters, lambda. */
final class Scope(val parent: Option[Scope], val description: String):
  val decls: mutable.LinkedHashMap[String, Sym] = mutable.LinkedHashMap.empty
  /** Ordering index of items processed so far (forward-reference check for meta definitions). */
  var processed: Int = -1

  def lookupLocal(name: String): Option[Sym] = decls.get(name)

  def lookup(name: String): Option[Sym] =
    decls.get(name).orElse(parent.flatMap(_.lookup(name)))

  def allNames: Iterator[String] = decls.keysIterator ++ parent.iterator.flatMap(_.allNames)

  def enter(s: Sym): Unit = decls(s.name) = s
