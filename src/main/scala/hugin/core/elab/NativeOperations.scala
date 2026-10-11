package hugin.core
package elab

import hugin.obj.ArithOp
import hugin.syntax.Literal

object NativeOperations:
  /** The library file whose functions get native operations (the standard library's path, not a name in
   *  scope: a program's own `plus` is an ordinary function). */
  val NatPath: String = hugin.compiler.SourceLoader.StdlibPrefix + "std/nat.hgn"

  /** The functions of `std/nat` with their operations, in the order they are checked (an operation's
   *  equations may use the operations before it: `times` uses `plus`). */
  val operations: List[(Name, NatOp)] = List(
    "plus" -> NatOp.Add,
    "minus" -> NatOp.Monus,
    "times" -> NatOp.Mul,
    "divSucAux" -> NatOp.DivSucAux,
    "modSucAux" -> NatOp.ModSucAux,
    "equal" -> NatOp.Eq,
    "less" -> NatOp.Lt,
    "toInt" -> NatOp.ToInt
  )

/** The native operations of `std/nat` (reference: std/nat, native arithmetic; issue #131), bound as Lean
 *  binds `Nat.add` and checked as Agda's `verify`: when the file `std/nat` has been elaborated, each of
 *  its functions named in [[NativeOperations.operations]] is checked against the defining equations of
 *  its operation, by conversion on fresh variables, and then records the operation in its body
 *  ([[FunctionBody.native]]), so that it computes on numbers when all its arguments are numerals
 *  ([[NatArithmetic]]). The equations determine the function on all numerals by induction, so the
 *  numbers and the clauses agree. A failed check is an internal error: the library is wrong, not the
 *  program. */
trait NativeOperations:
  self: Elaborator =>
  import core.*

  /** Binds the operations of `std/nat`, if this file is it. */
  def bindNativeOperations(): Unit =
    if file.path == NativeOperations.NatPath && !file.signaturesOnly then
      for (name, op) <- NativeOperations.operations; id <- scope.get(name) if declaredHere(id) do bindNative(id, op)

  private def declaredHere(id: Int): Boolean =
    globals(id).span.exists && globals(id).span.source.path == file.path

  private def bindNative(id: Int, op: NatOp): Unit =
    val g = globals(id)
    def wrong(why: String): Nothing = throw Impossible(s"std/nat: `${g.name}` is not the native ${op.key}: $why")
    g.kind match
      case GlobalKind.Function(arity, Some(body)) if arity == op.arity =>
        val (binders, result) = telescope(g.ty)
        if binders.length != arity || binders.exists(_._2 != Icit.Expl) then wrong("its type has other arguments")
        val (_, suc) = natType(binders.head._3).getOrElse(wrong("its first argument is not nat-like"))
        val fam = force(binders.head._3) match
          case Val.Rigid(Head.Glob(f), Nil) => f
          case _ => wrong("its first argument is not a family")
        val ctors = op match
          case NatOp.Eq | NatOp.Lt =>
            force(result) match
              case Val.Rigid(Head.Glob(b), Nil) =>
                globals(b).kind match
                  case GlobalKind.Inductive(cs @ List(_, _)) => cs
                  case _ => wrong("its result is not a boolean")
              case _ => wrong("its result is not a boolean")
          case _ => Nil
        val native = NativeNat(op, fam, ctors)
        val variants = equations(id, native, suc)
        if !variants.exists(_.forall((l, r) => conv(4, l, r))) then wrong("an equation does not hold")
        g.kind = GlobalKind.Function(arity, Some(body.copy(native = Some(native))))
        // hover: the description says that it is native
        val sym = symOf(id)
        index.description(sym).foreach(d => index.describe(sym, s"$d\n(native: ${op.key})"))
      case _ => wrong("it is not a function of that arity with clauses")

  /** The defining equations of the operation of `f` (Agda's, `Rules/Builtin.hs`), over the fresh variables
   *  `n`, `m`, … at levels 0 to 3: one list per accepted variant of the definition. */
  private def equations(f: Int, n: NativeNat, suc: Int): List[List[(Val, Val)]] =
    val List(x, y, z, w) = List(0, 1, 2, 3).map(Val.local)
    val z0: Val = Val.Nat(n.fam, BigInt(0))
    def s(v: Val): Val = app(Val.Rigid(Head.Glob(suc), Nil), v, Icit.Expl)
    def call(g: Int, args: Val*): Val = args.foldLeft(Val.Rigid(Head.Glob(g), Nil): Val)(app(_, _, Icit.Expl))
    def fn(args: Val*): Val = call(f, args*)
    def op(o: NatOp): Option[Int] =
      NativeOperations.operations.find(_._2 == o).flatMap((name, _) => scope.get(name)).filter { g =>
        globals(g).kind match
          case GlobalKind.Function(_, Some(b)) => b.native.exists(_.op == o)
          case _ => false
      }
    def bool(b: Boolean): Val = Val.Rigid(Head.Glob(if b then n.ctors(0) else n.ctors(1)), Nil)
    def int(k: Long): Val = Val.Lit(Literal.IntL(k), Stage.S1)
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
      case NatOp.ToInt =>
        List(List(fn(z0) -> int(0), fn(s(x)) -> arith(ArithOp.Add, fn(x), int(1), Stage.S1)))
