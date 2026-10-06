package hugin.ir

import hugin.obj.{ArithOp, CmpOp, Rule, Query, RelSym}
import hugin.syntax.AggKind

/** Words (Section 9.1): literals (java.lang.Long, java.lang.Double, String) or identities. */
final case class Id(rel: Int, n: Int)

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

  /** Look up the identity of an existing fact (no interning). */
  case Lookup(dst: Int, rel: Int, args: Array[Expr])
  case NotIn(ops: Array[BodyOp])
  case Agg(dst: Int, kind: AggKind, term: Expr, locals: Array[Int], ops: Array[BodyOp])

/** A compiled rule: body operations followed by the head (Insert). */
final class CompiledRule(
    val source: Rule,
    val nregs: Int,
    val body: Array[BodyOp],
    val headRel: Int,
    val headArgs: Array[Expr],
    val recursiveAtoms: Int
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

final class CoreProgram(
    val rels: Vector[RelSym],
    /** Components in evaluation order, as relation tags. */
    val components: Vector[Vector[Int]],
    val rules: Vector[CompiledRule],
    val queries: Vector[CompiledQuery],
    /** Bound-column sets per relation that need an index. */
    val indexes: Map[Int, Set[Vector[Int]]]
)
