package hugin.ir

import hugin.obj.{ArithOp, CmpOp, Rule, Query, RelDirectives, RelSym}
import hugin.syntax.AggKind

/** Words (Section 9.1): literals (java.lang.Long, java.lang.Double, String) or identities. */
final case class Id(rel: Int, n: Int)

/** The value of a constructor term in a comparison that was never built. It differs from every
 *  identity (an existing value would have been found) and equals another absent value of the same
 *  structure, so a comparison does not depend on which values happen to exist. It occurs only in tests,
 *  never in a fact. */
final case class Absent(rel: Int, args: Vector[Any])

/** Which part of a relation a scan reads (Section 9.5). */
enum Version:
  case Full, Old, Delta

/** Expressions over registers. */
enum Expr:
  case Reg(r: Int)
  case Const(w: Any)
  case Arith(op: ArithOp, l: Expr, r: Expr)
  case Neg(e: Expr)

  /** Head construction of a nested fact (Make), possibly nested. */
  case Make(rel: Int, args: Array[Expr])

/** Body operations of the core IR (Section 9.3). Registers are slots of a per-rule register file. */
enum BodyOp:
  /** Iterate facts of `rel` (`recIdx` ≥ 0 for atoms of the current component, which get versions). */
  case Scan(rel: Int, recIdx: Int, asReg: Int, binds: Array[(Int, Int)], checks: Array[(Int, Expr)])

  /** `src` holds an identity: look up its tuple. */
  case Deref(src: Int, rel: Int, binds: Array[(Int, Int)], checks: Array[(Int, Expr)])
  case Tag(src: Int, tags: Set[Int])
  case Eval(dst: Int, e: Expr)
  case Test(op: CmpOp, a: Expr, b: Expr)

  /** Look up the identity of an existing value (no interning). If it was never built, the operation fails,
   *  or with `orAbsent` (operands of comparisons) yields an [[Absent]] value. */
  case Lookup(dst: Int, rel: Int, args: Array[Expr], orAbsent: Boolean = false)
  case NotIn(ops: Array[BodyOp])
  case Agg(dst: Int, kind: AggKind, term: Expr, locals: Array[Int], ops: Array[BodyOp])

/** A compiled rule: body operations followed by the head (Insert). */
final class CompiledRule(
    val source: Rule,
    val nregs: Int,
    val body: Array[BodyOp],
    val headRel: Int,
    val headArgs: Array[Expr],
    val recursiveAtoms: Int,
    /** Head columns whose constructed values are probes: interned, not asserted. These are the input
     *  columns of demand relations and, in a rule of a moded relation guarded by the demand of mode `m`,
     *  the inputs of `m`. Values built in other columns are facts, with the values nested in them. */
    val probeCols: Set[Int] = Set.empty
)

final class CompiledQuery(
    val source: Query,
    val nregs: Int,
    /** One plan per alternative (projection expansion / disjunction). */
    val alternatives: Array[Array[BodyOp]],
    /** User variables and their register in each alternative. */
    val vars: List[String],
    val regs: Array[Array[Int]]
)

/** A compiled program. Relations are referred to by tag: their index in `rels`. */
final class CoreProgram(
    val rels: Vector[RelSym],
    /** The directives of each relation, by tag. */
    val directives: Vector[RelDirectives],
    /** Components in evaluation order, as relation tags. */
    val components: Vector[Vector[Int]],
    val rules: Vector[CompiledRule],
    val queries: Vector[CompiledQuery],
    /** Bound-column sets per relation that need an index. */
    val indexes: Map[Int, Set[Vector[Int]]]
):
  private val tags: Map[RelSym, Int] = rels.zipWithIndex.toMap

  /** The tag of a relation of the program. */
  def tag(r: RelSym): Int = tags(r)
