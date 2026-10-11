package hugin.core

import hugin.obj.BaseType
import hugin.syntax.Literal

/** The meta `int` of a compilation (reference: std/int; issue #186, D8): the inductive family `int` of
 *  `std/nat` with the constructors `ofNat : nat -> int` and `negSucc : nat -> int` (Lean 4's `Int`,
 *  `src/Init/Data/Int/Basic.lean`), over the nat-like family `natFam` of `std/nat`. */
final case class MetaInt(fam: Int, ofNat: Int, negSucc: Int, natFam: Int)

/** Integers of the meta level (reference: std/int). The base type `int` used as a meta type is the
 *  inductive family `int` of `std/nat` once that file is elaborated ([[registerMetaInt]]); before, and
 *  in a compilation without `std/nat`, it is the primitive `Val.Base(int, meta)`. A program compiled
 *  with `--no-prelude` then has no meta integers (E0928); only the elaborator's own tests elaborate bare
 *  files, in which its literals are primitive 64-bit values. A closed integer is represented as a number ([[Val.IntNum]], [[Tm.IntNum]]), as a
 *  closed numeral of a nat-like family is ([[Naturals]]), and code that inspects constructors sees it
 *  through [[Naturals.natView]]: `ofNat n` for `n ≥ 0`, `negSucc (-n - 1)` below. The clauses of
 *  `std/int` stay the definition of the operations; [[NatArithmetic]] computes them on numbers. */
trait Integers:
  self: Core =>

  private var registered: MetaInt | Null = null

  /** The functions of `std/int` that arithmetic on meta integers applies, by operation key (`add`,
   *  `sub`, `mul`, `div`, `neg`), once that file is elaborated. */
  private var operators: Map[String, Int] = Map.empty

  protected def copyIntegers(from: Integers): Unit =
    registered = from.registered
    operators = from.operators

  /** The meta `int`, if `std/nat` has been elaborated. */
  def metaInt: MetaInt | Null = registered

  def registerMetaInt(m: MetaInt): Unit = registered = m

  /** The function of `std/int` for an arithmetic operation on meta integers. */
  def intOperator(key: String): Option[Int] = operators.get(key)

  def registerIntOperators(ops: Map[String, Int]): Unit = operators = ops

  /** For a function of `std/int` that an operator applies: the operator (`+`, `-`, `*`, `/`, and `-x`
   *  for negation), as printing shows its applications. */
  def intOperatorSymbol(id: Int): Option[String] =
    if operators.isEmpty then None
    else operators.collectFirst { case (k, `id`) => Integers.symbols(k) }

  /** The meta `int` as a value: the family, or the primitive while there is none. */
  def metaIntType: Val =
    val m = registered
    if m == null then Val.Base(BaseType.IntT, Stage.S1) else Val.Rigid(Head.Glob(m.fam), Nil)

  /** Whether `v` (forced) is the meta `int`. */
  def isMetaInt(v: Val): Boolean = v match
    case Val.Base(BaseType.IntT, Stage.S1) => true
    case Val.Rigid(Head.Glob(f), Nil) =>
      val m = registered
      m != null && m.fam == f
    case _ => false

  /** The base type of a meta primitive, the meta `int` included (`v` forced). */
  def metaBase(v: Val): Option[BaseType] = v match
    case Val.Base(b, Stage.S1) => Some(b)
    case f if isMetaInt(f) => Some(BaseType.IntT)
    case _ => None

  /** Whether `id` is the family of the meta `int`. */
  def isMetaIntFamily(id: Int): Boolean =
    val m = registered
    m != null && m.fam == id

  /** The meta primitive `int` and its literals as values of the family, once there is one: the types and
   *  terms that the compiler built before `std/nat` was elaborated (the type of `std/reflect`'s `tint`),
   *  and the literals of reflection, are the family's. */
  final def intForm(v: Val): Val =
    val m = registered
    if m == null then v
    else
      v match
        case Val.Base(BaseType.IntT, Stage.S1) => Val.Rigid(Head.Glob(m.fam), Nil)
        case Val.Lit(Literal.IntL(k), Stage.S1) => Val.IntNum(BigInt(k))
        case other => other

  /** The constructor `c` of the meta `int` applied to `a`: the integer if `a` is a numeral. */
  def intOfConstructor(c: Int, a: Val): Option[Val] =
    val m = registered
    if m == null || (c != m.ofNat && c != m.negSucc) then None
    else
      numeral(a) match
        case Val.Nat(f, k) if f == m.natFam => Some(Val.IntNum(if c == m.ofNat then k else -k - 1))
        case _ => None

  /** An integer seen as a constructor application: `ofNat n` or `negSucc n` with the numeral `n`. */
  def intView(n: BigInt): Val =
    val m = registered.nn
    if n >= 0 then Val.Rigid(Head.Glob(m.ofNat), List(Elim.EApp(Val.Nat(m.natFam, n), Icit.Expl)))
    else Val.Rigid(Head.Glob(m.negSucc), List(Elim.EApp(Val.Nat(m.natFam, -n - 1), Icit.Expl)))

  /** [[intView]] on terms. */
  def intViewTm(n: BigInt): Tm =
    val m = registered.nn
    if n >= 0 then Tm.App(Tm.Global(m.ofNat), Tm.Nat(m.natFam, n), Icit.Expl)
    else Tm.App(Tm.Global(m.negSucc), Tm.Nat(m.natFam, -n - 1), Icit.Expl)

object Integers:
  /** The operators of the meta `int` by the key of the `std/int` function they apply. */
  val symbols: Map[String, String] = Map("add" -> "+", "sub" -> "-", "mul" -> "*", "div" -> "/", "neg" -> "-x")

  /** The range of the object level's `int`, which a meta integer must be in to be used as object code
   *  (reference: meta/staging, lifting; D8a). */
  def fits64(n: BigInt): Boolean = n.isValidLong
