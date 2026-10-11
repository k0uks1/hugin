package hugin.core
package elab

object NativeOperations:
  /** The library files whose functions get native operations (the standard library's paths, not names in
   *  scope: a program's own `plus` is an ordinary function). */
  val NatPath: String = hugin.compiler.SourceLoader.StdlibPrefix + "std/nat.hgn"
  val IntPath: String = hugin.compiler.SourceLoader.StdlibPrefix + "std/int.hgn"

  /** The functions of `std/nat` with their operations, in the order they are checked (an operation's
   *  equations may use the operations before it: `times` uses `plus`). */
  val operations: List[(Name, NatOp)] = List(
    "plus" -> NatOp.Add,
    "minus" -> NatOp.Monus,
    "times" -> NatOp.Mul,
    "divSucAux" -> NatOp.DivSucAux,
    "modSucAux" -> NatOp.ModSucAux,
    "equal" -> NatOp.Eq,
    "less" -> NatOp.Lt
  )

  /** The functions of `std/int` with their operations, in the order they are checked (their equations use
   *  the operations of `std/nat` and those before them). */
  val intOperations: List[(Name, NatOp)] = List(
    "negOfNat" -> NatOp.NegOfNat,
    "subNatNat" -> NatOp.SubNatNat,
    "ineg" -> NatOp.IntNeg,
    "iplus" -> NatOp.IntAdd,
    "iminus" -> NatOp.IntSub,
    "itimes" -> NatOp.IntMul,
    "idiv" -> NatOp.IntDiv,
    "iequal" -> NatOp.IntEq,
    "iless" -> NatOp.IntLt,
    "ileq" -> NatOp.IntLe,
    "fits64" -> NatOp.Fits64,
    "natAbs" -> NatOp.NatAbs
  )

  /** The functions of `std/int` that the arithmetic operators on meta integers apply, by the key of
   *  [[Integers.symbols]]. */
  val intOperators: List[(String, Name)] =
    List("add" -> "iplus", "sub" -> "iminus", "mul" -> "itimes", "div" -> "idiv", "neg" -> "ineg")

/** The native operations of `std/nat` and `std/int` (reference: std/nat and std/int, native arithmetic;
 *  issues #131 and #186), bound as Lean binds `Nat.add` and checked as Agda's `verify`: when one of these
 *  files has been elaborated, each of its functions named in [[NativeOperations.operations]] (or
 *  [[NativeOperations.intOperations]]) is checked against the defining equations of its operation, by
 *  conversion on fresh variables, and then records the operation in its body ([[FunctionBody.native]]),
 *  so that it computes on numbers when all its arguments are numerals ([[NatArithmetic]]). The equations
 *  determine the function on all numerals (by induction for `std/nat`, by the two constructors of `int`
 *  over the checked operations of `std/nat` for `std/int`), so the numbers and the clauses agree. A failed
 *  check is an internal error: the library is wrong, not the program.
 *
 *  The same step makes the family `int` of `std/nat` the meta `int` ([[Integers]]) and records the
 *  functions of `std/int` that the arithmetic operators apply. */
trait NativeOperations:
  self: Elaborator =>
  import core.*

  /** Binds the operations of `std/nat` or `std/int`, if this file is one of them. */
  def bindNativeOperations(): Unit =
    if file.path == NativeOperations.NatPath then
      registerInt()
      if !file.signaturesOnly then
        for (name, op) <- NativeOperations.operations; id <- scope.get(name) if declaredHere(id) do bindNative(id, op)
    else if file.path == NativeOperations.IntPath && metaInt != null then
      val ops = for (key, name) <- NativeOperations.intOperators; id <- scope.get(name) if declaredHere(id) yield key -> id
      registerIntOperators(ops.toMap)
      if !file.signaturesOnly then
        for (name, op) <- NativeOperations.intOperations; id <- scope.get(name) if declaredHere(id) do bindNative(id, op)

  /** The family `int` of `std/nat`, with its constructors `ofNat` and `negSucc`, as the meta `int`. */
  private def registerInt(): Unit =
    def wrong(why: String): Nothing = throw Impossible(s"std/nat: `int` is not the meta int: $why")
    for fam <- scope.get("int") if declaredHere(fam) do
      globals(fam).kind match
        case GlobalKind.Inductive(List(of, neg)) if globals(of).name == "ofNat" && globals(neg).name == "negSucc" =>
          val natFam = force(globals(of).ty) match
            case Val.Pi(_, Icit.Expl, a, _) =>
              force(a) match
                case Val.Rigid(Head.Glob(n), Nil) if natLike(n).isDefined => n
                case _ => wrong("the argument of `ofNat` is not nat-like")
            case _ => wrong("`ofNat` has no argument")
          registerMetaInt(MetaInt(fam, of, neg, natFam))
        case _ => wrong("its constructors are not `ofNat` and `negSucc`")

  private def declaredHere(id: Int): Boolean =
    globals(id).span.exists && globals(id).span.source.path == file.path

  private def bindNative(id: Int, op: NatOp): Unit =
    val g = globals(id)
    val lib = if file.path == NativeOperations.IntPath then "std/int" else "std/nat"
    def wrong(why: String): Nothing = throw Impossible(s"$lib: `${g.name}` is not the native ${op.key}: $why")
    g.kind match
      case GlobalKind.Function(arity, Some(body)) if arity == op.arity =>
        val (binders, result) = telescope(g.ty)
        if binders.length != arity || binders.exists(_._2 != Icit.Expl) then wrong("its type has other arguments")
        // the nat-like family of the natural numbers among its arguments and results
        val fam =
          if lib == "std/int" then metaInt.nn.natFam
          else
            force(binders.head._3) match
              case Val.Rigid(Head.Glob(f), Nil) if natLike(f).isDefined => f
              case _ => wrong("its first argument is not nat-like")
        val (_, suc) = natLike(fam).get
        val ctors =
          if op.isComparison then
            force(result) match
              case Val.Rigid(Head.Glob(b), Nil) =>
                globals(b).kind match
                  case GlobalKind.Inductive(cs @ List(_, _)) => cs
                  case _ => wrong("its result is not a boolean")
              case _ => wrong("its result is not a boolean")
          else Nil
        val native = NativeNat(op, fam, ctors)
        val variants = equations(id, native, suc)
        if !variants.exists(_.forall((l, r) => conv(4, l, r))) then
          val failed = variants.flatten.find((l, r) => !conv(4, l, r)).map((l, r) => s" (${quote(4, l)} = ${quote(4, r)})").getOrElse("")
          wrong(s"an equation does not hold$failed")
        g.kind = GlobalKind.Function(arity, Some(body.copy(native = Some(native))))
        // hover: the description says that it is native
        val sym = symOf(id)
        index.description(sym).foreach(d => index.describe(sym, s"$d\n(native: ${op.key})"))
      case _ => wrong("it is not a function of that arity with clauses")

  /** The defining equations of the operation of `f` (Agda's, `Rules/Builtin.hs`; for `std/int` Lean's
   *  definitions, `src/Init/Data/Int/Basic.lean`), over the fresh variables `n`, `m`, … at levels 0 to 3:
   *  one list per accepted variant of the definition. */
  private def equations(f: Int, n: NativeNat, suc: Int): List[List[(Val, Val)]] =
    val List(x, y, z, w) = List(0, 1, 2, 3).map(Val.local)
    val z0: Val = Val.Nat(n.fam, BigInt(0))
    def s(v: Val): Val = app(Val.Rigid(Head.Glob(suc), Nil), v, Icit.Expl)
    def call(g: Int, args: Val*): Val = args.foldLeft(Val.Rigid(Head.Glob(g), Nil): Val)(app(_, _, Icit.Expl))
    def fn(args: Val*): Val = call(f, args*)
    /** The function bound to the operation `o` already (of `std/nat`, or one of `std/int` before `f`). */
    def op(o: NatOp): Option[Int] =
      (NativeOperations.operations ++ NativeOperations.intOperations).find(_._2 == o).flatMap((name, _) => lookupGlobal(name)).filter { g =>
        globals(g).kind match
          case GlobalKind.Function(_, Some(b)) => b.native.exists(_.op == o)
          case _ => false
      }
    def bool(b: Boolean): Val = Val.Rigid(Head.Glob(if b then n.ctors(0) else n.ctors(1)), Nil)
    // the integers: the constructors of the meta `int` over natural numbers
    lazy val mi = metaInt.nn
    def ofNat(v: Val): Val = call(mi.ofNat, v)
    def negSucc(v: Val): Val = call(mi.negSucc, v)
    def int(k: Int): Val = Val.IntNum(BigInt(k))
    /** Equations over the operations `os` (all bound), or none if one is not. */
    def using(os: NatOp*)(eqs: Seq[Int] => List[(Val, Val)]): List[List[(Val, Val)]] =
      val ids = os.map(op)
      if ids.exists(_.isEmpty) then Nil else List(eqs(ids.map(_.get)))
    n.op match
      case NatOp.Add =>
        List(
          List(fn(x, z0) -> x, fn(x, s(y)) -> s(fn(x, y))),
          List(fn(z0, y) -> y, fn(s(x), y) -> s(fn(x, y)))
        )
      case NatOp.Monus =>
        List(List(fn(z0, z0) -> z0, fn(z0, s(y)) -> z0, fn(s(x), z0) -> s(x), fn(s(x), s(y)) -> fn(x, y)))
      case NatOp.Mul =>
        // `+` is the native add, in either order
        op(NatOp.Add).toList.flatMap { plus =>
          List(
            List(fn(x, z0) -> z0, fn(x, s(y)) -> call(plus, fn(x, y), x)),
            List(fn(x, z0) -> z0, fn(x, s(y)) -> call(plus, x, fn(x, y))),
            List(fn(z0, y) -> z0, fn(s(x), y) -> call(plus, y, fn(x, y))),
            List(fn(z0, y) -> z0, fn(s(x), y) -> call(plus, fn(x, y), y))
          )
        }
      case NatOp.DivSucAux =>
        List(
          List(
            fn(x, y, z0, w) -> x,
            fn(x, y, s(z), z0) -> fn(s(x), y, z, y),
            fn(x, y, s(z), s(w)) -> fn(x, y, z, w)
          )
        )
      case NatOp.ModSucAux =>
        List(
          List(
            fn(x, y, z0, w) -> x,
            fn(x, y, s(z), z0) -> fn(z0, y, z, y),
            fn(x, y, s(z), s(w)) -> fn(s(x), y, z, w)
          )
        )
      case NatOp.Eq =>
        List(
          List(
            fn(z0, z0) -> bool(true),
            fn(s(x), z0) -> bool(false),
            fn(z0, s(y)) -> bool(false),
            fn(s(x), s(y)) -> fn(x, y)
          )
        )
      case NatOp.Lt =>
        List(List(fn(x, z0) -> bool(false), fn(z0, s(y)) -> bool(true), fn(s(x), s(y)) -> fn(x, y)))
      // `std/int`: each function by the two constructors of each integer argument (Lean's definitions);
      // a natural-number argument by induction
      case NatOp.NegOfNat =>
        List(List(fn(z0) -> int(0), fn(s(x)) -> negSucc(x)))
      case NatOp.SubNatNat =>
        List(List(fn(x, z0) -> ofNat(x), fn(z0, s(y)) -> negSucc(y), fn(s(x), s(y)) -> fn(x, y)))
      case NatOp.IntNeg =>
        using(NatOp.NegOfNat) { ids =>
          val negOfNat = ids(0)
         
          List(fn(ofNat(x)) -> call(negOfNat, x), fn(negSucc(x)) -> ofNat(s(x)))
        }
      case NatOp.IntAdd =>
        using(NatOp.Add, NatOp.SubNatNat) { ids =>
          val plus = ids(0); val subNatNat = ids(1)
         
          List(
            fn(ofNat(x), ofNat(y)) -> ofNat(call(plus, x, y)),
            fn(ofNat(x), negSucc(y)) -> call(subNatNat, x, s(y)),
            fn(negSucc(x), ofNat(y)) -> call(subNatNat, y, s(x)),
            fn(negSucc(x), negSucc(y)) -> negSucc(s(call(plus, x, y)))
          )
        }
      case NatOp.IntSub =>
        using(NatOp.IntAdd, NatOp.IntNeg) { ids =>
          val add = ids(0); val neg = ids(1)
          List(fn(x, y) -> call(add, x, call(neg, y))) }
      case NatOp.IntMul =>
        using(NatOp.Mul, NatOp.NegOfNat) { ids =>
          val times = ids(0); val negOfNat = ids(1)
         
          List(
            fn(ofNat(x), ofNat(y)) -> ofNat(call(times, x, y)),
            fn(ofNat(x), negSucc(y)) -> call(negOfNat, call(times, x, s(y))),
            fn(negSucc(x), ofNat(y)) -> call(negOfNat, call(times, s(x), y)),
            fn(negSucc(x), negSucc(y)) -> ofNat(call(times, s(x), s(y)))
          )
        }
      case NatOp.IntDiv =>
        // division by a successor `d + 1` is `divSucAux 0 d n d`
        using(NatOp.DivSucAux, NatOp.NegOfNat) { ids =>
          val divSucAux = ids(0); val negOfNat = ids(1)
         
          def div(a: Val, d: Val) = call(divSucAux, z0, d, a, d)
          List(
            fn(ofNat(x), ofNat(z0)) -> int(0),
            fn(ofNat(x), ofNat(s(y))) -> ofNat(div(x, y)),
            fn(ofNat(x), negSucc(y)) -> call(negOfNat, div(x, y)),
            fn(negSucc(x), ofNat(z0)) -> int(0),
            fn(negSucc(x), ofNat(s(y))) -> call(negOfNat, div(s(x), y)),
            fn(negSucc(x), negSucc(y)) -> ofNat(div(s(x), y))
          )
        }
      case NatOp.IntEq =>
        using(NatOp.Eq) { ids =>
          val equal = ids(0)
         
          List(
            fn(ofNat(x), ofNat(y)) -> call(equal, x, y),
            fn(ofNat(x), negSucc(y)) -> bool(false),
            fn(negSucc(x), ofNat(y)) -> bool(false),
            fn(negSucc(x), negSucc(y)) -> call(equal, x, y)
          )
        }
      case NatOp.IntLt =>
        using(NatOp.Lt) { ids =>
          val less = ids(0)
         
          List(
            fn(ofNat(x), ofNat(y)) -> call(less, x, y),
            fn(ofNat(x), negSucc(y)) -> bool(false),
            fn(negSucc(x), ofNat(y)) -> bool(true),
            fn(negSucc(x), negSucc(y)) -> call(less, y, x)
          )
        }
      case NatOp.IntLe =>
        using(NatOp.Lt) { ids =>
          val less = ids(0)
         
          List(
            fn(ofNat(x), ofNat(y)) -> call(less, x, s(y)),
            fn(ofNat(x), negSucc(y)) -> bool(false),
            fn(negSucc(x), ofNat(y)) -> bool(true),
            fn(negSucc(x), negSucc(y)) -> call(less, y, s(x))
          )
        }
      case NatOp.Fits64 =>
        // within -2^63 … 2^63 - 1: `ofNat n` and `negSucc n` for `n < 2^63`
        using(NatOp.Lt) { ids =>
          val less = ids(0)
         
          val bound = Val.Nat(n.fam, BigInt(2).pow(63))
          List(fn(ofNat(x)) -> call(less, x, bound), fn(negSucc(x)) -> call(less, x, bound))
        }
      case NatOp.NatAbs =>
        List(List(fn(ofNat(x)) -> x, fn(negSucc(x)) -> s(x)))
