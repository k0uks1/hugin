package hugin.obj

import hugin.util.*
import hugin.meta.MExpr

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

/** Type parameter of a family (Section 4.6). */
final class TParam(val name: String):
  val id: Int = TParam.next()
  override def toString: String = name
object TParam:
  private var n = 0
  private def next(): Int = { n += 1; n }

private object SymIds:
  private var n = 0
  def next(): Int = { n += 1; n }

enum TypeKind:
  /** `a : type.` — open type of facts. */
  case Open

  /** `a : type <: b.` — nominal refinement of a base type or refinement. */
  case Refinement(base: OType)

/** An object type constant (open type or refinement), possibly a family. */
final class TypeSym(val name: String, var kind: TypeKind, val span: Span, val origin: Origin):
  val id: Int = SymIds.next()
  var tparams: List[TParam] = Nil

  /** For family instances: the generic family and the type arguments. */
  var instanceOf: Option[(TypeSym, List[OType])] = None
  def isOpen: Boolean = kind == TypeKind.Open
  def displayName: String = instanceOf.map(_._1.displayName).getOrElse(name)
  override def toString: String = name

final case class Column(label: Option[String], tpe: OType)

enum RelKind:
  case Plain, Ctor, Struct

  /** Demand relation d^c_m of Section 7.3. */
  case Demand(of: RelSym, mode: Mode)

  /** Derivation relation @r#i of Section 7.4. */
  case Derivation(rule: String)

  /** Auxiliary relation introduced by the compiler, e.g. for a disjunction inside an aggregate. */
  case Auxiliary(purpose: String)

/** A mode: `true` = input (+), `false` = output (-). */
final case class Mode(inputs: Vector[Boolean]):
  def show: String = inputs.map(b => if b then "+" else "-").mkString
  def arity: Int = inputs.length
object Mode:
  def allOut(n: Int): Mode = Mode(Vector.fill(n)(false))

/** An object relation (plain relation, constructor or struct). The fact type has the same name. */
final class RelSym(val name: String, var kind: RelKind, val span: Span, val origin: Origin):
  val id: Int = SymIds.next()
  var tparams: List[TParam] = Nil
  var cols: Vector[Column] = Vector.empty

  /** `None` for plain relations (ω = rel); the open result type for constructors. */
  var result: Option[OType] = None
  var instanceOf: Option[(RelSym, List[OType])] = None
  // directives
  var modes: List[(Mode, Span)] = Nil
  var isOpen = false
  var isPartial = false
  var isInput = false
  var isOutput = false

  /** `%terminates`: the measured argument positions (lexicographic if several) and the directive. */
  var terminates: Option[(List[Int], Span)] = None
  var derivations = false
  var nameHint: Option[String] = None

  /** Runtime index (assigned during lowering). */
  var tag: Int = -1

  def arity: Int = cols.length
  def isCtor: Boolean = kind == RelKind.Ctor
  def isDemand: Boolean = kind match { case RelKind.Demand(_, _) => true; case _ => false }
  def isDerivation: Boolean = kind match { case RelKind.Derivation(_) => true; case _ => false }

  /** Source name used in output: qualified, without type arguments. */
  def displayName: String = instanceOf.map(_._1.displayName).getOrElse(name)
  def labelIndex(l: String): Option[Int] = cols.indexWhere(_.label.contains(l)) match
    case -1 => None
    case k => Some(k)
  def hasModes: Boolean = modes.nonEmpty
  override def toString: String = name

/** Object types (Figure 2), plus forms that only exist before monomorphization or meta evaluation. */
enum OType:
  case Base(b: BaseType)
  case Con(sym: TypeSym, args: List[OType])
  case Fact(rel: RelSym, args: List[OType])
  case RelTop
  case Union(members: List[OType])

  /** Family type parameter (before monomorphization). */
  case Param(p: TParam)

  /** Unification variable used by monomorphization. */
  case Meta(id: Int)

  /** Splice of a meta expression of meta type `type` (before meta evaluation). */
  case Splice(m: MExpr)
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
    case Con(s, as) => (s.name :: as.map(showArg)).mkString(" ")
    case Fact(r, Nil) => r.name
    case Fact(r, as) => (r.name :: as.map(showArg)).mkString(" ")
    case RelTop => "rel"
    case Union(ms) => ms.map(show).mkString(" | ")
    case Param(p) => p.name
    case Meta(id) => s"?$id"
    case Splice(m) => s"~(${MExpr.show(m)})"
    case Err => "<error>"

  /** As an argument of a type application: compound types in parentheses. */
  def showArg(t: OType): String = t match
    case Con(_, _ :: _) | Fact(_, _ :: _) | Union(_) => s"(${show(t)})"
    case _ => show(t)

  def subst(t: OType, m: Map[TParam, OType]): OType = if m.isEmpty then t
  else
    t match
      case Param(p) => m.getOrElse(p, t)
      case Con(s, as) => Con(s, as.map(subst(_, m)))
      case Fact(r, as) => Fact(r, as.map(subst(_, m)))
      case Union(ms) => union(ms.map(subst(_, m)))
      case other => other

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
    case Param(_) | Meta(_) | Splice(_) | Err => true
    case _ => false
  }
