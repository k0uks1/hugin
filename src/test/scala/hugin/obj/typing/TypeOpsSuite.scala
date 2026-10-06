package hugin.obj
package typing

import hugin.util.*

class TypeOpsSuite extends munit.FunSuite:
  private def rel(name: String, result: Option[OType] = None): RelSym =
    val r = RelSym(name, if result.isDefined then RelKind.Ctor else RelKind.Plain, Span.NoSpan, Origin.Source)
    r.result = result
    r
  // expr : type.  lam, app : ... -> expr.  var : rel (plain), var <: expr.  age : type <: int.
  private val expr = TypeSym("expr", TypeKind.Open, Span.NoSpan, Origin.Source)
  private val age = TypeSym("age", TypeKind.Refinement(OType.Int), Span.NoSpan, Origin.Source)
  private val lam = rel("lam", Some(OType.Con(expr, Nil)))
  private val app = rel("app", Some(OType.Con(expr, Nil)))
  private val v = rel("var")
  private val other = rel("other")
  private val prog = ObjProgram(
    Vector(expr, age),
    Vector(lam, app, v, other),
    Vector(Edge(OType.Fact(v, Nil), expr)(Span.NoSpan, Origin.Source)),
    Vector.empty,
    Vector.empty,
    Vector.empty
  )
  private val ops = TypeOps(prog)
  private def f(r: RelSym) = OType.Fact(r, Nil)
  private val exprT = OType.Con(expr, Nil)

  test("subtyping: constructors, edges, rel, refinements (Section 5.5)") {
    assert(ops.isSub(f(lam), exprT))
    assert(ops.isSub(f(v), exprT))
    assert(!ops.isSub(f(other), exprT))
    assert(ops.isSub(exprT, OType.RelTop))
    assert(ops.isSub(OType.Con(age, Nil), OType.Int))
    assert(!ops.isSub(OType.Int, OType.Con(age, Nil)))
    assert(ops.isSub(OType.union(List(f(lam), f(app))), exprT))
  }

  test("members of open types include edge sources (Definition 5.2)") {
    assertEquals(ops.members(exprT), Set(lam, app, v))
    assertEquals(ops.members(OType.RelTop), Set(lam, app, v, other))
  }

  test("closed types are fact types and unions of them") {
    assert(ops.isClosed(OType.union(List(f(lam), f(app)))))
    assert(!ops.isClosed(exprT))
  }

  test("meets (Definition 6.1)") {
    assertEquals(ops.meet(exprT, f(lam)), Some(f(lam)))
    assertEquals(ops.meet(OType.union(List(f(lam), f(other))), exprT), Some(f(lam)))
    assertEquals(ops.meet(f(lam), f(app)), None)
    assertEquals(ops.meet(OType.Con(age, Nil), OType.Int), Some(OType.Con(age, Nil)))
    assertEquals(ops.meet(OType.Int, OType.Str), None)
    assertEquals(ops.meet(OType.Int, exprT), None)
  }
