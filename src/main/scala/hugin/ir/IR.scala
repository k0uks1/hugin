package hugin.ir

import hugin.obj.{ArithOp, CmpOp, Rule, Query, RelDirectives, RelSym}
import hugin.syntax.AggKind

/** Words (Section 9.1): literals (java.lang.Long, java.lang.Double, String), identities, or the infinite
 *  values of integer columns (`hugin.runtime.Infinity`, reference: object/bound-columns). */
final case class Id(rel: Int, n: Int)

/** The value, in a comparison, of a constructor term that is not a fact (reference: object/facts: bodies never
 *  create facts). Every value bound in a satisfying valuation has only facts as constructor subterms, so such a term differs from every bound value; two of them are
 *  equal if they have the same structure. Comparisons are therefore structural without asserting or
 *  interning the term. It occurs only as an operand of a test, never in a register binding or a fact. */
final case class NonFact(rel: Int, args: Vector[Any])

/** Which part of a relation a scan reads (Section 9.5). */
enum Version:
  case Full, Old, Delta

/** Expressions over registers. */
enum Expr:
  case Reg(r: Int)
  case Const(w: Any)
  case Arith(op: ArithOp, l: Expr, r: Expr)
  case Neg(e: Expr)

  /** A constructor term `c t̄`. In a head it is asserted (the constructor subterms of a head are facts,
   *  `subfact_F`). In a body (comparison operands, binding equations) it is looked up: its identity if it
   *  is a fact, otherwise a [[NonFact]]. */
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

  /** The existence check of a fact-constructor term in a binding equation (`X = c t̄`, read as
   *  `(c t̄ as X)`): the identity of the fact, or failure if `c t̄` is not a fact. It reads `rel` like an
   *  atom: `recIdx` ≥ 0 if `rel` belongs to the current component, and the check then sees only the
   *  version (old, delta, full) of the round, like a [[Scan]] (issue #83). */
  case Lookup(dst: Int, rel: Int, recIdx: Int, args: Array[Expr])
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
    /** Registers holding the identities of the tuples matched by the atoms of the component whose bound
     *  column flows into the head's bound column: the edges of the value propagation graph. */
    val limitRegs: Array[Int] = Array.empty
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
