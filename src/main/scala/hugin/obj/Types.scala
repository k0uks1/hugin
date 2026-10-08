package hugin.obj

import hugin.util.*

enum BaseType:
  case IntT, FloatT, StringT
  def show: String = this match
    case IntT => "int"
    case FloatT => "float"
    case StringT => "string"

object BaseType:
  def of(l: hugin.syntax.Literal): BaseType = l match
    case hugin.syntax.Literal.IntL(_) => IntT
    case hugin.syntax.Literal.FloatL(_) => FloatT
    case hugin.syntax.Literal.StrL(_) => StringT

/** Ids of object symbols: unique, and increasing in creation order (members of a closed type are ordered
 *  by id). Compilations may run on several threads (the fuzz suites, a language server and a REPL in one
 *  process), so the counter is atomic. */
private object SymIds:
  private val n = java.util.concurrent.atomic.AtomicInteger()
  def next(): Int = n.incrementAndGet()

enum TypeKind:
  /** `a : type.` — open type of facts. */
  case Open

  /** `a : type <: b.` — nominal refinement of a base type or refinement. */
  case Refinement(base: OType)

/** An object type constant (open type or refinement), possibly a family. */
final class TypeSym(val name: String, var kind: TypeKind, val span: Span, val origin: Origin):
  val id: Int = SymIds.next()

  /** For family instances: the generic family and the type arguments. */
  var instanceOf: Option[(TypeSym, List[OType])] = None
  def isOpen: Boolean = kind == TypeKind.Open
  def displayName: String = instanceOf.map(_._1.displayName).getOrElse(name)
  override def toString: String = name

/** A column of a relation or constructor; `bound` marks a bound column (`min τ` / `max τ`, only the last
 *  column of a relation, checked by [[hugin.obj.check.BoundColumnsPhase]]). */
final case class Column(label: Option[String], tpe: OType, bound: Option[hugin.syntax.Bound] = None)

enum RelKind:
  case Plain, Ctor, Struct

  /** Derivation relation @r#i of Section 7.4. */
  case Derivation(rule: String)

  /** Auxiliary relation introduced by the compiler, e.g. for a disjunction inside an aggregate. */
  case Auxiliary(purpose: String)

/** An object relation (plain relation, constructor or struct). The fact type has the same name. Its
 *  declaration (`cols`, `result`, `instanceOf`) is filled in when the symbol is created, by the handover
 *  from the meta level or the phase that introduces it; what later phases learn about it is in
 *  [[ProgramFacts]] (directives) and the core IR (runtime tags). Every constructor and struct is a fact
 *  constructor (REDESIGN §3.2), also the relation of its facts. */
final class RelSym(val name: String, val kind: RelKind, val span: Span, val origin: Origin):
  val id: Int = SymIds.next()
  var cols: Vector[Column] = Vector.empty

  /** `None` for plain relations (ω = rel); the open result type for constructors. */
  var result: Option[OType] = None
  var instanceOf: Option[(RelSym, List[OType])] = None

  def arity: Int = cols.length

  /** The kind of the relation's bound column (`min τ` / `max τ`, docs/REDESIGN.md §5.2), which is its last
   *  column; `None` for constructors (bound columns are only allowed on relations, E0605). */
  def boundColumn: Option[hugin.syntax.Bound] =
    if kind == RelKind.Ctor || kind == RelKind.Struct then None else cols.lastOption.flatMap(_.bound)
  def isCtor: Boolean = kind == RelKind.Ctor

  def isDerivation: Boolean = kind match { case RelKind.Derivation(_) => true; case _ => false }

  /** Source name used in output: qualified, without type arguments. */
  def displayName: String = instanceOf.map(_._1.displayName).getOrElse(name)
  def labelIndex(l: String): Option[Int] = cols.indexWhere(_.label.contains(l)) match
    case -1 => None
    case k => Some(k)
  override def toString: String = name

/** Object types (Figure 2). */
enum OType:
  case Base(b: BaseType)
  case Con(sym: TypeSym, args: List[OType])
  case Fact(rel: RelSym, args: List[OType])
  case RelTop
  case Union(members: List[OType])
  case Err

  def show: String = OType.show(this)

object OType:
  val Int: OType = Base(BaseType.IntT)
  val Float: OType = Base(BaseType.FloatT)
  val Str: OType = Base(BaseType.StringT)

  def union(ts: List[OType]): OType =
    val flat = ts.flatMap {
      case Union(ms) => ms
      case t => List(t)
    }.distinct
    flat match
      case Nil => Err
      case List(t) => t
      case many => Union(many)

  def show(t: OType): String = t match
    case Base(b) => b.show
    case Con(s, Nil) => s.name
    case Con(s, as) => (s.name :: as.map(showArg(_))).mkString(" ")
    case Fact(r, Nil) => r.name
    case Fact(r, as) => (r.name :: as.map(showArg(_))).mkString(" ")
    case RelTop => "rel"
    case Union(ms) => ms.map(show(_)).mkString(" | ")
    case Err => "<error>"

  /** As an argument of a type application: compound types in parentheses. */
  def showArg(t: OType): String = t match
    case Con(_, _ :: _) | Fact(_, _ :: _) | Union(_) => s"(${show(t)})"
    case _ => show(t)

  def mapDeep(t: OType)(f: PartialFunction[OType, OType]): OType =
    if f.isDefinedAt(t) then f(t)
    else
      t match
        case Con(s, as) => Con(s, as.map(mapDeep(_)(f)))
        case Fact(r, as) => Fact(r, as.map(mapDeep(_)(f)))
        case Union(ms) => union(ms.map(mapDeep(_)(f)))
        case other => other

  def exists(t: OType)(p: OType => Boolean): Boolean =
    p(t) || (t match
      case Con(_, as) => as.exists(exists(_)(p))
      case Fact(_, as) => as.exists(exists(_)(p))
      case Union(ms) => ms.exists(exists(_)(p))
      case _ => false
    )

  def isGround(t: OType): Boolean = !exists(t) {
    case Err => true
    case _ => false
  }
