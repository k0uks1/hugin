package hugin.core

import hugin.obj.BaseType
import hugin.syntax.Literal
import hugin.util.Span

/** Conversion checking (definitional equality) of values without metavariables. */
class ConversionSuite extends munit.FunSuite:
  import Tm.*

  private val E = Icit.Expl
  private def conv(core: Core, a: Tm, b: Tm): Boolean = core.conv(0, core.eval(Nil, a), core.eval(Nil, b))

  private def withPostulates(core: Core, names: String*): Map[String, Int] =
    names.map { n =>
      n -> core.addGlobal(GlobalEntry(n, core.eval(Nil, U1(Level.zero)), U1(Level.zero), Stage.S1, GlobalKind.Postulate, Span.NoSpan))
    }.toMap

  test("α-equivalence and β") {
    val core = Core()
    val g = withPostulates(core, "a", "b")
    assert(conv(core, Lam("x", E, Var(0)), Lam("y", E, Var(0))))
    assert(conv(core, App(Lam("x", E, Var(0)), Global(g("a")), E), Global(g("a"))))
    assert(!conv(core, Global(g("a")), Global(g("b"))))
  }

  test("η for functions") {
    val core = Core()
    val g = withPostulates(core, "f")
    assert(conv(core, Lam("x", E, App(Global(g("f")), Var(0), E)), Global(g("f"))))
    assert(conv(core, Global(g("f")), Lam("x", E, App(Global(g("f")), Var(0), E))))
  }

  test("η for records") {
    val core = Core()
    val g = withPostulates(core, "r")
    val r = Global(g("r"))
    assert(conv(core, Rec(List("a" -> Proj(r, "a"), "b" -> Proj(r, "b"))), r))
    assert(!conv(core, Rec(List("a" -> Proj(r, "b"))), r))
  }

  test("Π types: domains and codomains, icitness") {
    val core = Core()
    val int = Base(BaseType.IntT, Stage.S1)
    assert(conv(core, Pi("x", E, int, int), Pi("y", E, int, int)))
    assert(!conv(core, Pi("x", E, int, int), Pi("x", Icit.Impl, int, int)))
    assert(!conv(core, Pi("x", E, int, int), Pi("x", E, int, Base(BaseType.StringT, Stage.S1))))
  }

  test("stages are distinguished") {
    val core = Core()
    assert(!conv(core, Base(BaseType.IntT, Stage.S0), Base(BaseType.IntT, Stage.S1)))
    assert(!conv(core, Lit(Literal.IntL(1), Stage.S0), Lit(Literal.IntL(1), Stage.S1)))
    assert(conv(core, Lift(Base(BaseType.IntT, Stage.S0)), Lift(Base(BaseType.IntT, Stage.S0))))
    assert(conv(core, Quote(Splice(Quote(Lit(Literal.IntL(1), Stage.S0)))), Quote(Lit(Literal.IntL(1), Stage.S0))))
  }

  test("universe levels: equal levels are convertible, distinct constants are not") {
    val core = Core()
    assert(conv(core, U1(Level.zero), U1(Level.zero)))
    assert(!conv(core, U1(Level.zero), U1(Level.const(1))))
    val l = core.levels.fresh()
    assert(conv(core, U1(l), U1(Level.const(2))))
    assertEquals(core.levels.value(l), 2)
  }
