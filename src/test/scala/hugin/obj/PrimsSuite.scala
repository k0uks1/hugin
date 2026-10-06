package hugin.obj

import hugin.syntax.Literal.*

class PrimsSuite extends munit.FunSuite:
  test("integer arithmetic is 64-bit and partial (Section 3.3)") {
    assertEquals(Prims.arith(ArithOp.Add, IntL(2), IntL(3)), Some(IntL(5)))
    assertEquals(Prims.arith(ArithOp.Add, IntL(Long.MaxValue), IntL(1)), None)
    assertEquals(Prims.arith(ArithOp.Mul, IntL(Long.MinValue), IntL(-1)), None)
    assertEquals(Prims.arith(ArithOp.Div, IntL(7), IntL(0)), None)
    assertEquals(Prims.arith(ArithOp.Div, IntL(Long.MinValue), IntL(-1)), None)
    assertEquals(Prims.arith(ArithOp.Div, IntL(-7), IntL(2)), Some(IntL(-3)))
    assertEquals(Prims.neg(IntL(Long.MinValue)), None)
  }

  test("ints and floats are never converted into each other") {
    assertEquals(Prims.arith(ArithOp.Add, IntL(1), FloatL(1.0)), None)
    assertEquals(Prims.arith(ArithOp.Concat, StrL("a"), StrL("b")), Some(StrL("ab")))
    assertEquals(Prims.arith(ArithOp.Add, StrL("a"), StrL("b")), None)
  }

  test("float division by zero is undefined") {
    assertEquals(Prims.arith(ArithOp.Div, FloatL(1.0), FloatL(0.0)), None)
  }

  test("strings compare by code point, not by UTF-16 unit") {
    // U+1F600 is encoded with surrogates (0xD83D...), which sort below U+FFFD in UTF-16
    assert(Prims.cmp(CmpOp.Gt, StrL("😀"), StrL("�")))
    assert(Prims.cmp(CmpOp.Lt, StrL("ab"), StrL("abc")))
    assert(Prims.cmp(CmpOp.Ne, IntL(1), FloatL(1.0)))
  }
