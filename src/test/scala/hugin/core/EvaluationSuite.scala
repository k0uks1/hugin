package hugin.core

import hugin.obj.{ArithOp, BaseType}
import hugin.syntax.Literal
import hugin.util.Span

/** Normalisation by evaluation: β, δ (definitions), quote/splice cancellation, records, compile-time
 *  arithmetic, read-back of binders. */
class EvaluationSuite extends munit.FunSuite:
  import Tm.*

  private def int(n: Long, st: Stage = Stage.S1) = Lit(Literal.IntL(n), st)
  private val E = Icit.Expl
  private def nf(core: Core, t: Tm) = core.showTm(Nil, core.nf(Nil, t))

  test("β-reduction under binders, read-back with names") {
    val core = Core()
    val id = Lam("x", E, Var(0))
    val k = Lam("x", E, Lam("y", E, Var(1)))
    assertEquals(nf(core, App(id, int(1), E)), "1")
    assertEquals(nf(core, App(k, id, E)), "[y] [x] x")
    // (λf. λx. f (f x)) applied to (λy. y + 1) and 3 computes at compile time
    val twice = Lam("f", E, Lam("x", E, App(Var(1), App(Var(1), Var(0), E), E)))
    val inc = Lam("y", E, Arith(ArithOp.Add, Var(0), int(1), Stage.S1))
    assertEquals(nf(core, App(App(twice, inc, E), int(3), E)), "5")
  }

  test("neutral terms stay stuck") {
    val core = Core()
    val f = Lam("f", E, Lam("x", E, App(Var(1), Var(0), E)))
    assertEquals(nf(core, f), "[f] [x] f x")
    assertEquals(nf(core, Lam("x", E, Arith(ArithOp.Add, Var(0), int(1), Stage.S1))), "[x] x + 1")
  }

  test("object arithmetic is code, meta arithmetic computes") {
    val core = Core()
    assertEquals(nf(core, Arith(ArithOp.Mul, int(6, Stage.S0), int(7, Stage.S0), Stage.S0)), "6 * 7")
    assertEquals(nf(core, Arith(ArithOp.Mul, int(6), int(7), Stage.S1)), "42")
    // undefined compile-time arithmetic stays stuck (staging reports it)
    assertEquals(nf(core, Arith(ArithOp.Div, int(1), int(0), Stage.S1)), "1 / 0")
  }

  test("splices of quotes cancel; persistence of literals") {
    val core = Core()
    val c = Lit(Literal.StrL("a"), Stage.S0)
    assertEquals(core.nf(Nil, Splice(Quote(c))), c)
    assertEquals(nf(core, Lam("x", E, Quote(Splice(Var(0))))), "[x] x")
    assertEquals(core.nf(Nil, Persist(int(42))), int(42, Stage.S0))
  }

  test("records: projection and dependent field types") {
    val core = Core()
    val r = Rec(List("a" -> int(1), "b" -> int(2)))
    assertEquals(nf(core, Proj(r, "b")), "2")
    // { t : Type, x : t } — the type of x is the value of t
    val rt = core.eval(Nil, RecTy(List("t" -> U1(Level.zero), "x" -> Var(0)))).asInstanceOf[Val.RecTy]
    val v = core.eval(Nil, Rec(List("t" -> Base(BaseType.IntT, Stage.S1), "x" -> int(3))))
    assertEquals(core.fieldType(rt, v, "x").map(core.showVal(Nil, _)), Some("int"))
  }

  test("definitions unfold, postulates are neutral") {
    val core = Core()
    val ty = core.eval(Nil, Base(BaseType.IntT, Stage.S1))
    val p = core.addGlobal(GlobalEntry("p", ty, Base(BaseType.IntT, Stage.S1), Stage.S1, GlobalKind.Postulate, Span.NoSpan))
    val d = core.addGlobal(GlobalEntry(
      "d",
      ty,
      Base(BaseType.IntT, Stage.S1),
      Stage.S1,
      GlobalKind.Definition(int(7), core.eval(Nil, int(7))),
      Span.NoSpan
    ))
    assertEquals(nf(core, Arith(ArithOp.Add, Global(p), Global(d), Stage.S1)), "p + 7")
  }

  test("zonk substitutes solved metas but keeps elaborated structure") {
    val core = Core()
    val m = core.newMeta(core.eval(Nil, Base(BaseType.IntT, Stage.S1)), Stage.S1, Span.NoSpan, "m")
    core.solveMeta(m, core.eval(Nil, int(3)))
    val t = Lam("x", E, Quote(Splice(App(Var(0), Meta(m), E))))
    assertEquals(core.showTm(Nil, core.zonk(Nil, 0, t)), "[x] x 3")
  }
