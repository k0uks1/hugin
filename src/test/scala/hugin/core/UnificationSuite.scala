package hugin.core

import hugin.util.Span

/** Higher-order pattern unification: the pattern fragment, pruning, intersection, flex-flex problems,
 *  eta-expansion of metas along `⇑` and records, and the failures (occurs check, scope escape,
 *  non-patterns, universe levels). */
class UnificationSuite extends munit.FunSuite:
  import Tm.*

  private val E = Icit.Expl

  /** A core with a postulated meta type `A : Type₀` and postulates `p : A`, `g : A -> A`. */
  private final class Fixture:
    val core = Core()
    private def postulate(n: String, ty: Tm, st: Stage = Stage.S1): Int =
      core.addGlobal(GlobalEntry(n, core.eval(Nil, ty), ty, st, GlobalKind.Postulate, Span.NoSpan))
    val A: Int = postulate("A", U1(Level.zero))
    val p: Int = postulate("p", Global(A))
    val g: Int = postulate("g", Pi("_", E, Global(A), Global(A)))
    val obj: Int = postulate("obj", U0, Stage.S0)
    val c: Int = postulate("c", Global(obj), Stage.S0)

    /** A meta of type `A -> … -> A` (`arity` arguments) or of a given closed type. */
    def meta(arity: Int): Int =
      val ty = (0 until arity).foldLeft(Global(A): Tm)((acc, _) => Pi("x", E, Global(A), acc))
      core.newMeta(core.eval(Nil, ty), Stage.S1, Span.NoSpan, "m")
    def metaOf(ty: Tm, st: Stage = Stage.S1): Int = core.newMeta(core.eval(Nil, ty), st, Span.NoSpan, "m")

    def x(l: Int): Val = Val.local(l)
    def flex(m: Int, args: Val*): Val = Val.Flex(m, args.toList.reverse.map(Elim.EApp(_, E)))
    def glob(id: Int, args: Val*): Val = core.appSp(core.globalValue(id), args.toList.reverse.map(Elim.EApp(_, E)))
    def solution(m: Int): String = core.metas(m).solution.map(core.showVal(Nil, _)).getOrElse("unsolved")
    def unify(l: Int, a: Val, b: Val): Unit = core.unify(l, a, b)
    def failure(l: Int, a: Val, b: Val): UnifyFailure = intercept[UnifyError](core.unify(l, a, b)).failure

  test("pattern: a meta applied to distinct variables is solved by inversion") {
    val f = Fixture()
    val m = f.meta(2)
    f.unify(2, f.flex(m, f.x(0), f.x(1)), f.glob(f.g, f.x(1)))
    assertEquals(f.solution(m), "[x] [x'] g x'")
  }

  test("occurs check") {
    val f = Fixture()
    val m = f.meta(1)
    assertEquals(f.failure(1, f.flex(m, f.x(0)), f.glob(f.g, f.flex(m, f.x(0)))), UnifyFailure.Occurs(m))
  }

  test("scope escape: the solution cannot mention a variable the meta is not applied to") {
    val f = Fixture()
    val m = f.meta(1)
    assert(f.failure(2, f.flex(m, f.x(0)), f.x(1)).isInstanceOf[UnifyFailure.Escape])
  }

  test("non-pattern spines are rejected") {
    val f = Fixture()
    val m = f.meta(1)
    assertEquals(f.failure(1, f.flex(m, f.glob(f.g, f.x(0))), f.x(0)), UnifyFailure.NonPattern)
  }

  test("non-linear spines: repeated variables are pruned, so they cannot occur in the solution") {
    val f = Fixture()
    val m = f.meta(2)
    f.unify(1, f.flex(m, f.x(0), f.x(0)), f.glob(f.p))
    assertEquals(f.solution(m), "[x] [x'] p")
    val m2 = f.meta(2)
    assert(f.failure(1, f.flex(m2, f.x(0), f.x(0)), f.x(0)).isInstanceOf[UnifyFailure.Escape])
  }

  test("pruning: a meta on the right-hand side loses the arguments outside the renaming") {
    val f = Fixture()
    val m = f.meta(1)
    val n = f.meta(2)
    // ?m x =? g (?n x y): ?n cannot depend on y
    f.unify(2, f.flex(m, f.x(0)), f.glob(f.g, f.flex(n, f.x(0), f.x(1))))
    assert(f.solution(n).matches("""\[x\] \[x'\] \?\d+ x"""), f.solution(n))
    assert(f.solution(m).matches("""\[x\] g \(\?\d+ x\)"""), f.solution(m))
  }

  test("intersection: ?m x y =? ?m y x prunes both arguments") {
    val f = Fixture()
    val m = f.meta(2)
    f.unify(2, f.flex(m, f.x(0), f.x(1)), f.flex(m, f.x(1), f.x(0)))
    assert(f.solution(m).matches("""\[x\] \[x'\] \?\d+"""), f.solution(m))
  }

  test("flex-flex with different metas") {
    val f = Fixture()
    val m = f.meta(2)
    val n = f.meta(1)
    f.unify(2, f.flex(m, f.x(0), f.x(1)), f.flex(n, f.x(0)))
    assert(f.solution(m) == s"[x] [x'] ?$n x" || f.solution(n) != "unsolved")
  }

  test("a spliced meta of type ⇑A is eta-expanded to a quote") {
    val f = Fixture()
    val m = f.metaOf(Lift(Global(f.obj)))
    f.unify(0, Val.Flex(m, List(Elim.ESplice)), f.glob(f.c))
    assertEquals(f.solution(m), "⟨c⟩")
  }

  test("a projected meta of record type is eta-expanded to a record") {
    val f = Fixture()
    val m = f.metaOf(RecTy(List("a" -> Global(f.A), "b" -> Global(f.A))))
    f.unify(0, Val.Flex(m, List(Elim.EProj("a"))), f.glob(f.p))
    assert(f.solution(m).matches("""\{ a = p, b = \?\d+ \}"""), f.solution(m))
  }

  test("the solution of a meta of type Type₀ must be in Type₀") {
    val f = Fixture()
    val m = f.metaOf(U1(Level.zero))
    assertEquals(f.failure(0, Val.Flex(m, Nil), Val.U1(Level.zero)), UnifyFailure.Universe)
    val m2 = f.metaOf(U1(Level.const(1)))
    f.unify(0, Val.Flex(m2, Nil), Val.U1(Level.zero))
    assertEquals(f.solution(m2), "Type")
  }

  test("rigid mismatches") {
    val f = Fixture()
    assertEquals(f.failure(0, f.glob(f.p), f.glob(f.g, f.glob(f.p))), UnifyFailure.Mismatch)
    assertEquals(f.failure(0, Val.U0, Val.U1(Level.zero)), UnifyFailure.Mismatch)
  }

  // Frozen metas (issue #66): the metas created before a block are not solved or pruned inside it.

  test("frozen: a meta of an earlier block is not solved") {
    val f = Fixture()
    val m = f.meta(0)
    f.core.inBlock {
      assertEquals(f.failure(0, f.flex(m), f.glob(f.p)), UnifyFailure.Frozen(m))
      assertEquals(f.failure(0, f.glob(f.p), f.flex(m)), UnifyFailure.Frozen(m))
    }
    assertEquals(f.solution(m), "unsolved")
    // outside blocks (staging) it is solvable again
    f.unify(0, f.flex(m), f.glob(f.p))
    assertEquals(f.solution(m), "p")
  }

  test("frozen: against an active meta, the active one is solved") {
    val f = Fixture()
    val old = f.meta(0)
    f.core.inBlock {
      val fresh = f.meta(0)
      f.unify(0, f.flex(old), f.flex(fresh))
      assertEquals(f.solution(old), "unsolved")
      assertEquals(f.solution(fresh), "?0")
    }
  }

  test("frozen: the same frozen meta on both sides compares the spines") {
    val f = Fixture()
    val m = f.meta(1)
    f.core.inBlock {
      f.unify(1, f.flex(m, f.x(0)), f.flex(m, f.x(0)))
      assertEquals(f.failure(2, f.flex(m, f.x(0)), f.flex(m, f.x(1))), UnifyFailure.Mismatch)
      assertEquals(f.solution(m), "unsolved")
    }
  }

  test("frozen: a frozen meta in a solution is not pruned") {
    val f = Fixture()
    val old = f.meta(2)
    f.core.inBlock {
      val fresh = f.meta(1)
      // ?fresh x0 = g (?old x0 x1): x1 is out of scope, and ?old may not be pruned
      assertEquals(f.failure(2, f.flex(fresh, f.x(0)), f.glob(f.g, f.flex(old, f.x(0), f.x(1)))), UnifyFailure.Escape(1))
      assertEquals(f.solution(old), "unsolved")
    }
  }

  test("frozen: blocks inside a block are part of it") {
    val f = Fixture()
    f.core.inBlock {
      val m = f.meta(0)
      f.core.inBlock(f.unify(0, f.flex(m), f.glob(f.p)))
      assertEquals(f.solution(m), "p")
    }
  }

  // Approximate conversion (issue #66, Batch 3): smalltt's states Rigid, Flex and Full.

  /** A definition `name : ty = tm` in the fixture's core. */
  private def define(f: Fixture, name: String, ty: Tm, tm: Tm): Int =
    f.core.addGlobal(GlobalEntry(name, f.core.eval(Nil, ty), ty, Stage.S1, GlobalKind.Definition(tm, f.core.eval(Nil, tm)), Span.NoSpan))

  private val AtoAtoA = (f: Fixture) => Pi("x", E, Global(f.A), Pi("y", E, Global(f.A), Global(f.A)))

  test("approximate: the same definition with different arguments is unfolded when the arguments differ") {
    val f = Fixture()
    val k = define(f, "k", AtoAtoA(f), Lam("x", E, Lam("y", E, Var(1))))
    // k p (g p) = k p p: the arguments differ, the values (both p) agree
    f.unify(0, f.glob(k, f.glob(f.p), f.glob(f.g, f.glob(f.p))), f.glob(k, f.glob(f.p), f.glob(f.p)))
    assertEquals(f.failure(0, f.glob(k, f.glob(f.p), f.glob(f.p)), f.glob(k, f.glob(f.g, f.glob(f.p)), f.glob(f.p))), UnifyFailure.Mismatch)
  }

  test("approximate: Flex solves no meta and unfolds no definition") {
    val f = Fixture()
    val m = f.meta(0)
    assertEquals(intercept[UnifyError](f.core.unify(0, f.flex(m), f.glob(f.p), ConvState.Flex)).failure, UnifyFailure.FlexSolution)
    assertEquals(f.solution(m), "unsolved")
    val d = define(f, "d", Global(f.A), App(Global(f.g), Global(f.p), E))
    intercept[UnifyError](f.core.unify(0, f.glob(d), f.glob(f.g, f.glob(f.p)), ConvState.Flex))
    // in the default state the definition is unfolded
    f.unify(0, f.glob(d), f.glob(f.g, f.glob(f.p)))
  }

  test("approximate: Flex adds no universe level constraint") {
    val f = Fixture()
    val a = f.core.levels.fresh()
    val b = f.core.levels.fresh()
    assertEquals(intercept[UnifyError](f.core.unify(0, Val.U1(a), Val.U1(b), ConvState.Flex)).failure, UnifyFailure.Universe)
    // a < b is still possible: no a = b was added
    assert(f.core.levels.lt(a, b))
  }

  test("approximate: an unknown is solved with the folded definition, also after unfolding") {
    val f = Fixture()
    val d = define(f, "d", Global(f.A), App(Global(f.g), Global(f.p), E))
    val k = define(f, "k", AtoAtoA(f), Lam("x", E, Lam("y", E, Var(1))))
    val m = f.meta(0)
    // k ?m p = k d p: the arguments do not match without solving ?m, so both sides are unfolded (Full)
    f.unify(0, f.glob(k, f.flex(m), f.glob(f.p)), f.glob(k, f.glob(d), f.glob(f.p)))
    assertEquals(f.solution(m), "d")
  }

  test("approximate: of two definitions the later one is unfolded first") {
    val f = Fixture()
    val d = define(f, "d", Global(f.A), App(Global(f.g), Global(f.p), E))
    val alias = define(f, "alias", Global(f.A), Global(d))
    f.unify(0, f.glob(alias), f.glob(d))
    f.unify(0, f.glob(d), f.glob(alias))
    f.unify(0, f.glob(alias), f.glob(f.g, f.glob(f.p)))
  }
