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
    def nat(x: BigInt) = Val.Nat(n.fam, x)
    def bool(b: Boolean) = Val.Rigid(Head.Glob(if b then n.ctors(0) else n.ctors(1)), Nil)
    (n.op, xs) match
      case (NatOp.Add, List(a, b)) => Some(nat(a + b))
      case (NatOp.Monus, List(a, b)) => Some(nat((a - b).max(0)))
      case (NatOp.Mul, List(a, b)) => Some(nat(a * b))
      // Agda's `primNatDivSucAux` and `primNatModSucAux`
      case (NatOp.DivSucAux, List(k, m, x, j)) => Some(nat(k + (x + m - j).max(0) / (m + 1)))
      case (NatOp.ModSucAux, List(k, m, x, j)) => Some(nat(if x > j then (x - j - 1) % (m + 1) else k + x))
      case (NatOp.Eq, List(a, b)) => Some(bool(a == b))
      case (NatOp.Lt, List(a, b)) => Some(bool(a < b))
      case (NatOp.NegOfNat, List(a)) => Some(Val.IntNum(-a))
      case (NatOp.SubNatNat, List(a, b)) => Some(Val.IntNum(a - b))
      case (NatOp.IntNeg, List(a)) => Some(Val.IntNum(-a))
      case (NatOp.IntAdd, List(a, b)) => Some(Val.IntNum(a + b))
      case (NatOp.IntSub, List(a, b)) => Some(Val.IntNum(a - b))
      case (NatOp.IntMul, List(a, b)) => Some(Val.IntNum(a * b))
      // truncated toward zero, as the object level's (and Lean's `Int.tdiv`); `x / 0` is `0`
      case (NatOp.IntDiv, List(a, b)) => Some(Val.IntNum(if b == 0 then BigInt(0) else a / b))
      case (NatOp.IntEq, List(a, b)) => Some(bool(a == b))
      case (NatOp.IntLt, List(a, b)) => Some(bool(a < b))
      case (NatOp.IntLe, List(a, b)) => Some(bool(a <= b))
      case (NatOp.Fits64, List(a)) => Some(bool(Integers.fits64(a)))
      case (NatOp.NatAbs, List(a)) => Some(nat(a.abs))
      case _ => throw Impossible(s"native ${n.op.key} on ${xs.length} arguments")
