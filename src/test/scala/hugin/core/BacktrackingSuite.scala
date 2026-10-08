package hugin.core

import hugin.core.elab.NameScope
import org.scalacheck.{Gen, Prop}
import scala.collection.mutable

/** The trails that replaced snapshots (issue #60) behave as the snapshots did: [[NameScope]] against a
 *  `LinkedHashMap` with the old "keep the names that were there" rollback, [[Levels]] against copies of
 *  its whole state, on random operations with nested transactions. */
class BacktrackingSuite extends munit.ScalaCheckSuite:
  private enum Op:
    case Put(n: String, v: Int)
    case Remove(n: String)
    case Begin
    case End(rollback: Boolean)

  private val names = Gen.oneOf("a", "b", "c", "d", "e")
  private val ops: Gen[List[Op]] = Gen.listOf(
    Gen.frequency(
      4 -> Gen.zip(names, Gen.choose(0, 9)).map(Op.Put.apply),
      2 -> names.map(Op.Remove.apply),
      1 -> Gen.const(Op.Begin),
      1 -> Gen.oneOf(true, false).map(Op.End.apply)
    )
  )

  property("NameScope: contents and order as a LinkedHashMap; a rollback drops the names added since") {
    Prop.forAll(ops) { ops =>
      val scope = NameScope()
      val ref = mutable.LinkedHashMap.empty[String, Int]
      val marks = mutable.Stack.empty[(Int, Set[String])]
      for op <- ops do
        op match
          case Op.Put(n, v) => scope(n) = v; ref(n) = v
          case Op.Remove(n) => scope.remove(n); ref.remove(n)
          case Op.Begin => marks.push((scope.begin(), ref.keySet.toSet))
          case Op.End(rollback) if marks.nonEmpty =>
            val (mark, before) = marks.pop()
            if rollback then
              scope.rollback(mark)
              ref.filterInPlace((n, _) => before(n))
            else scope.commit(mark)
          case Op.End(_) =>
      val copy = scope.copy()
      copy("z") = 1
      scope.toList == ref.toList && !scope.contains("z")
    }
  }

  private enum LevelOp:
    case Fresh
    case Le(a: Int, ak: Int, b: Int, bk: Int)
    case Eq(a: Int, b: Int)
    case Begin
    case End(rollback: Boolean)

  private val levelOps: Gen[List[LevelOp]] = Gen.listOf(
    Gen.frequency(
      2 -> Gen.const(LevelOp.Fresh),
      4 -> Gen.zip(Gen.choose(0, 6), Gen.choose(0, 2), Gen.choose(0, 6), Gen.choose(0, 2)).map(LevelOp.Le.apply),
      1 -> Gen.zip(Gen.choose(0, 6), Gen.choose(0, 6)).map(LevelOp.Eq.apply),
      1 -> Gen.const(LevelOp.Begin),
      1 -> Gen.oneOf(true, false).map(LevelOp.End.apply)
    )
  )

  property("Levels: a rollback returns to the state at the checkpoint, as a copy of the state did") {
    Prop.forAll(levelOps) { ops =>
      val levels = Levels()
      val marks = mutable.Stack.empty[(Levels.Checkpoint, (Vector[Int], Vector[List[(Int, Int)]]))]
      var ok = true
      def level(v: Int) = if v == 0 || v >= levels.count then Level.const(v % 3) else Level(v, 0)
      for op <- ops do
        op match
          case LevelOp.Fresh => levels.fresh()
          case LevelOp.Le(a, ak, b, bk) =>
            val (x, y) = (level(a), level(b))
            levels.le(Level(x.v, x.k + ak), Level(y.v, y.k + bk))
          case LevelOp.Eq(a, b) => levels.eq(level(a), level(b))
          case LevelOp.Begin => marks.push((levels.checkpoint(), levels.snapshot()))
          case LevelOp.End(rollback) if marks.nonEmpty =>
            val (c, state) = marks.pop()
            if rollback then
              levels.rollback(c)
              ok &&= levels.snapshot() == state
            else levels.commit(c)
          case LevelOp.End(_) =>
      ok
    }
  }

  test("Core: forks do not see each other's solutions; undoOnFailure and tentatively undo solutions and new metas") {
    val c = Core()
    val sp = hugin.util.Span.NoSpan
    val m0 = c.newMeta(Val.U0, Stage.S1, sp, "m0")
    val m1 = c.newMeta(Val.U0, Stage.S1, sp, "m1")
    c.solveMeta(m1, Val.RelT)
    val f = c.fork()
    f.solveMeta(m0, Val.PropT)
    assertEquals(c.metas(m0).solution, None)
    c.solveMeta(m0, Val.RelT)
    assertEquals(f.metas(m0).solution, Some(Val.PropT))
    val g = f.fork()
    g.allowUnsolved(m0)
    assert(!f.metas(m0).allowUnsolved && g.metas(m0).allowUnsolved)
    intercept[IllegalStateException] {
      f.undoOnFailure {
        f.solveMeta(m1, Val.PropT)
        f.newMeta(Val.U0, Stage.S1, sp, "m2")
        f.tentatively(f.solveMeta(m0, Val.U0))
        assertEquals(f.metas(m0).solution, Some(Val.PropT))
        throw IllegalStateException("undo")
      }
    }
    assertEquals(f.metas.length, 2)
    assertEquals(f.metas(m1).solution, Some(Val.RelT))
    assertEquals(c.metas(m1).solution, Some(Val.RelT))
    assertEquals(g.metas(m1).solution, Some(Val.RelT))
    f.undoOnFailure(f.solveMeta(m1, Val.U0))
    assertEquals(f.metas(m1).solution, Some(Val.U0))
    assertEquals(c.metas(m1).solution, Some(Val.RelT))
  }
