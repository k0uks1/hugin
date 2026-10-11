package hugin.core

/** An operation of `std/nat` or `std/int` that the compiler computes on numbers (reference: std/nat and
 *  std/int, native arithmetic): Agda's built-in operations on natural numbers (`NATPLUS` … `NATLESS`),
 *  and the operations on the meta `int`, which Lean 4 compiles to GMP (`@[extern "lean_int_add"]`).
 *  `key` is how it is shown (`native: add`), `arity` its number of arguments (all explicit). */
enum NatOp(val key: String, val arity: Int):
  case Add extends NatOp("add", 2)
  case Monus extends NatOp("monus", 2)
  case Mul extends NatOp("mul", 2)
  case DivSucAux extends NatOp("divSucAux", 4)
  case ModSucAux extends NatOp("modSucAux", 4)
  case Eq extends NatOp("eq", 2)
  case Lt extends NatOp("lt", 2)
  // the meta `int` (`std/int`): the first two on natural numbers, the others on integers
  case NegOfNat extends NatOp("negOfNat", 1)
  case SubNatNat extends NatOp("subNatNat", 2)
  case IntNeg extends NatOp("int neg", 1)
  case IntAdd extends NatOp("int add", 2)
  case IntSub extends NatOp("int sub", 2)
  case IntMul extends NatOp("int mul", 2)
  case IntDiv extends NatOp("int div", 2)
  case IntEq extends NatOp("int eq", 2)
  case IntLt extends NatOp("int lt", 2)
  case IntLe extends NatOp("int le", 2)
  case Fits64 extends NatOp("fits64", 1)
  case NatAbs extends NatOp("natAbs", 1)

  /** Whether its result is a boolean (the constructors `true` and `false` of [[NativeNat.ctors]]). */
  def isComparison: Boolean = this match
    case Eq | Lt | IntEq | IntLt | IntLe | Fits64 => true
    case _ => false

/** The native computation of a function of `std/nat` or `std/int`: its operation, the nat-like family of
 *  its natural-number arguments and results, and for a comparison the constructors `true` and `false` of
 *  its result type. */
final case class NativeNat(op: NatOp, fam: Int, ctors: List[Int])

/** Native arithmetic on numerals (issue #131, as Agda's `primClauses` and Lean 4's `Nat.add`): a
 *  function of `std/nat` or `std/int` that has a [[NativeNat]] computes on [[Val.Nat]] and [[Val.IntNum]]
 *  numbers when all its arguments are numerals; otherwise its clauses run ([[Matching.matchFunction]]). The clauses stay the definition:
 *  the operation is attached only after they are checked against its equations
 *  ([[elab.NativeOperations]]), so both give the same numeral. */
trait NatArithmetic:
  self: Core =>

  /** The result of `n` on `args` (as many as its arity): `Some(Some(v))` if all are numerals (of its
   *  family, or integers), `Some(None)` if they are but the result is stuck (no operation is, since
   *  integers are unbounded), and `None` if an argument is not a numeral (its clauses run). The arguments are only looked through (folded
   *  definitions, solved metas, positions), not reduced: a neutral argument is never forced here. */
  def nativeResult(n: NativeNat, args: List[Val]): Option[Option[Val]] =
    (n.op, args) match
      // `plus e k` of an open `e` and a numeral `k` is `e + k`, what its clauses on the second argument
      // give after `k` steps: an offset, in one ([[Val.NatAdd]])
      case (NatOp.Add, List(e, k)) =>
        (numeral(e), numeral(k)) match
          case (Val.Nat(_, _), _) => nativeNumbers(n, args)
          case (_, Val.Nat(f, j)) if f == n.fam => Some(Some(natAdd(n.fam, e, j)))
          case _ => None
      case _ => nativeNumbers(n, args)

  private def nativeNumbers(n: NativeNat, args: List[Val]): Option[Option[Val]] =
    val ns = new Array[BigInt](args.length)
    var rest = args
    var k = 0
    while rest.nonEmpty do
      // the arguments are well typed: an integer is at a position of type `int`
      numeral(rest.head) match
        case Val.Nat(f, x) if f == n.fam => ns(k) = x
        case Val.IntNum(x) => ns(k) = x
        case _ => return None
      rest = rest.tail
      k += 1
    if k != n.op.arity then None else Some(computeNative(n, ns.toList))

  /** The operation `n` on numbers. */
  def computeNative(n: NativeNat, xs: List[BigInt]): Option[Val] =
    (n.op, xs) match
      // Agda's `primNatDivSucAux` and `primNatModSucAux`
      case (NatOp.DivSucAux, List(k, m, x, j)) => Some(Val.Nat(n.fam, k + (x + m - j).max(0) / (m + 1)))
      case (NatOp.ModSucAux, List(k, m, x, j)) => Some(Val.Nat(n.fam, if x > j then (x - j - 1) % (m + 1) else k + x))
      case (_, List(a)) if n.op.arity == 1 => Some(native1(n, a))
      // a result beyond the size limit is not computed: the application is stuck
      case (_, List(a, b)) if n.op.arity == 2 => Option(native2(n, a, b))
      case _ => throw Impossible(s"native ${n.op.key} on ${xs.length} arguments")

  private def bool(n: NativeNat, b: Boolean): Val = Val.Rigid(Head.Glob(if b then n.ctors(0) else n.ctors(1)), Nil)

  /** An operation of one argument on a number. */
  private def native1(n: NativeNat, a: BigInt): Val = n.op match
    case NatOp.NegOfNat | NatOp.IntNeg => Val.IntNum(-a)
    case NatOp.Fits64 => bool(n, Integers.fits64(a))
    case NatOp.NatAbs => Val.Nat(n.fam, a.abs)
    case op => throw Impossible(s"native ${op.key} on 1 argument")

  /** An operation of two arguments on numbers; null if its result would have more than
   *  [[NatArithmetic.MaxBits]] bits (the size limit of the compiler's numbers). */
  private def native2(n: NativeNat, a: BigInt, b: BigInt): Val | Null = n.op match
    case NatOp.Add | NatOp.IntAdd | NatOp.SubNatNat | NatOp.IntSub if a.bitLength.max(b.bitLength) >= NatArithmetic.MaxBits => null
    case NatOp.Mul | NatOp.IntMul if a.bitLength + b.bitLength > NatArithmetic.MaxBits => null
    case NatOp.Add => Val.Nat(n.fam, a + b)
    case NatOp.Monus => Val.Nat(n.fam, (a - b).max(0))
    case NatOp.Mul => Val.Nat(n.fam, a * b)
    case NatOp.Eq | NatOp.IntEq => bool(n, a == b)
    case NatOp.Lt | NatOp.IntLt => bool(n, a < b)
    case NatOp.IntLe => bool(n, a <= b)
    case NatOp.SubNatNat | NatOp.IntSub => Val.IntNum(a - b)
    case NatOp.IntAdd => Val.IntNum(a + b)
    case NatOp.IntMul => Val.IntNum(a * b)
    // truncated toward zero, as the object level's (and Lean's `Int.tdiv`); `x / 0` is `0`
    case NatOp.IntDiv => Val.IntNum(if b == 0 then BigInt(0) else a / b)
    case op => throw Impossible(s"native ${op.key} on 2 arguments")

  /** The number of a numeral argument (of the family `fam`, or an integer), or null. */
  private def numberOf(v: Val, fam: Int): BigInt | Null = numeral(v) match
    case Val.Nat(f, x) if f == fam => x
    case Val.IntNum(x) => x
    case _ => null

  /** The application of the function `f` to the arguments `sp` (innermost first) and then `a`, if `f` has
   *  a native operation of one or two arguments and these are exactly its arguments, all numerals: its
   *  value, computed without building the application ([[matchFunction]] computes the same); null
   *  otherwise. The arithmetic on meta integers takes this path at every operator. */
  final def nativeApplication(f: FunctionBody, a: Val, sp: Spine): Val | Null =
    val n = f.native match
      case Some(x) => x
      case None => return null
    if n.op.arity == 1 then
      if sp.nonEmpty then null
      else
        val x = numberOf(a, n.fam)
        if x == null then null
        else
          Matching.nativeSteps += 1
          native1(n, x.nn)
    else if n.op.arity == 2 then
      sp match
        case List(Elim.EApp(first, _)) =>
          val x = numberOf(first, n.fam)
          if x == null then null
          else
            val y = numberOf(a, n.fam)
            if y == null then null
            else
              val r = native2(n, x.nn, y.nn)
              if r != null then Matching.nativeSteps += 1
              r
        case _ => null
    else null

object NatArithmetic:
  /** The size limit of the numbers that native operations compute, in bits (2^24 bits, about five million
   *  decimal digits): a sum or product beyond it is not computed, and its application stays stuck, as
   *  Lean's and Agda's numbers end where memory does. A larger `BigInt` would overflow the JVM's
   *  `BigInteger` (2^31 bits) after a few more squarings. */
  inline val MaxBits = 1 << 24
