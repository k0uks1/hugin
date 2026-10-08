package hugin.util.diagnostics

import scala.language.implicitConversions

/** The `msg"…"` interpolator and the plain rendering of messages. */
class MsgSuite extends munit.FunSuite:
  test("arguments render through their DiagArg: code in backticks, prose as is") {
    val m = msg"relation ${Src("edge")} has ${2} columns, ${Lit("not three")}"
    assertEquals(m.plain, "relation `edge` has 2 columns, not three")
    assertEquals(m.segs.collect { case Seg.Code(s) => s }, Vector("edge"))
  }

  test("backticked text in literal parts becomes code, and plain text is reproduced exactly") {
    val m = msg"`%complete` may only occur in a signature"
    assertEquals(m.segs.head, Seg.Code("%complete"))
    assertEquals(m.plain, "`%complete` may only occur in a signature")
    assertEquals(Msg.text("an odd ` backtick").plain, "an odd ` backtick")
  }

  test("messages nest, and join with a separator") {
    val inner = msg"${Src("a")}"
    assertEquals(msg"one of $inner".plain, "one of `a`")
    assertEquals(Msg.join(List(msg"x", msg"y", msg"z"), ", ").plain, "x, y, z")
    assert(Msg.empty.isEmpty)
  }

  test("escapes are processed as by s-interpolation") {
    assertEquals(msg"a\tb".plain, "a\tb")
  }

  test("a bare String does not interpolate") {
    assert(compileErrors("""val s = "x"; msg"a $s"""").nonEmpty)
  }
