package hugin.core
package objtype

import hugin.obj.BaseType

/** The head of an object constant or object type as the object type system sees it: a global (an object
 *  constant of the program, also an instance of a family), or a variable of the elaboration context (a
 *  member of a module body, or a functor's parameter `g` projected to `g.node`). */
enum OHead:
  case G(id: Int)
  case L(lvl: Int, projs: List[String])

/** Object types (reference: object/types) as the object type system of the core works with them: base
 *  types, object types and fact types by their heads (with the arguments of a family application that
 *  is not an instance yet), `rel` (every fact), unions. `Unknown` is a type the core does not know (an
 *  unsolved unknown, an abstract parameter type in a meet): it is compatible with every type and never
 *  reported. `Err` is the type of a variable whose meet is empty (already reported). */
enum OTy:
  case Base(b: BaseType)
  case Con(h: OHead, args: List[OTy])
  case Fact(h: OHead, args: List[OTy])
  case RelTop
  case Union(members: List[OTy])
  case Unknown
  case Err

  /** Whether the type is or contains `Unknown` or `Err`. */
  def vague: Boolean = this match
    case Unknown | Err => true
    case Con(_, as) => as.exists(_.vague)
    case Fact(_, as) => as.exists(_.vague)
    case Union(ms) => ms.exists(_.vague)
    case _ => false

object OTy:
  val Int: OTy = Base(BaseType.IntT)
  val Float: OTy = Base(BaseType.FloatT)
  val Str: OTy = Base(BaseType.StringT)

  def union(ts: List[OTy]): OTy =
    val flat = ts.flatMap {
      case Union(ms) => ms
      case t => List(t)
    }.distinct
    flat match
      case Nil => Err
      case List(t) => t
      case many => Union(many)

/** A relation, constructor or struct as the object type system sees it: its name for messages, its
 *  columns (labels and types) and, for a constructor, its result type. */
final case class RelInfo(head: OHead, args: List[OTy], name: String, cols: Vector[(Option[String], OTy)], result: Option[OTy]):
  def fact: OTy = OTy.Fact(head, args)
  def labelIndex(l: String): Option[Int] = cols.indexWhere(_._1.contains(l)) match
    case -1 => None
    case k => Some(k)

/** What a head denotes. */
enum HeadKind:
  case Open
  case Refinement(base: OTy)
  case Relation(info: RelInfo)

  /** A type the core cannot see into: a functor's parameter type (abstract in the body). */
  case Abstract
