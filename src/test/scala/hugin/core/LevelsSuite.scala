package hugin.core

/** The universe level constraint solver: least solutions, cycles, upper bounds. */
class LevelsSuite extends munit.FunSuite:
  test("least solution grows with lower bounds") {
    val ls = Levels()
    val a = ls.fresh()
    val b = ls.fresh()
    assert(ls.le(a.succ, b))
    assertEquals((ls.value(a), ls.value(b)), (0, 1))
    assert(ls.le(Level.const(3), a))
    assertEquals((ls.value(a), ls.value(b)), (3, 4))
  }

  test("a strict cycle is inconsistent and leaves the solution unchanged") {
    val ls = Levels()
    val a = ls.fresh()
    val b = ls.fresh()
    assert(ls.le(a, b))
    assert(ls.le(b, a))
    assert(!ls.lt(a, b))
    assertEquals((ls.value(a), ls.value(b)), (0, 0))
  }

  test("upper bounds by constants") {
    val ls = Levels()
    val a = ls.fresh()
    assert(ls.le(a, Level.const(1)))
    assert(ls.le(Level.const(1), a))
    assert(!ls.le(Level.const(2), a))
    assert(!ls.le(Level.const(1), Level.zero))
    assert(ls.le(Level.zero, Level.const(1)))
  }

  test("equality is all-or-nothing") {
    val ls = Levels()
    val a = ls.fresh()
    assert(ls.le(a, Level.const(0)))
    assert(!ls.eq(a, Level.const(1)))
    assertEquals(ls.value(a), 0)
  }
