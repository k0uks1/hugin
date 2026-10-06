package hugin.lsp

import hugin.util.{SourceFile, Span}
import org.eclipse.lsp4j.Position

class PositionsSuite extends munit.FunSuite:
  private def src(text: String) = SourceFile.virtual("t.hgn", text)

  test("offsets and positions round-trip on ASCII text") {
    val s = src("a : rel.\nb : rel.\n\nc.")
    for off <- 0 to s.content.length do assertEquals(Positions.offset(s, Positions.position(s, off)), off)
    assertEquals(Positions.position(s, 9), Position(1, 0))
    assertEquals(Positions.position(s, s.content.length), Position(3, 2))
  }

  test("columns count UTF-16 code units, not code points") {
    // U+1F600 is a surrogate pair: two code units, one code point
    val s = src("p \"😀\" X.")
    val x = s.content.indexOf('X')
    assertEquals(Positions.position(s, x), Position(0, 7))
    assertEquals(s.columnOf(x), 6)
    assertEquals(Positions.offset(s, Position(0, 7)), x)
  }

  test("a column inside a surrogate pair maps to the start of the pair") {
    val s = src("\"😀\"")
    assertEquals(Positions.offset(s, Position(0, 2)), 1)
  }

  test("positions past the end of a line or the file are clamped") {
    val s = src("ab\r\ncd")
    assertEquals(Positions.offset(s, Position(0, 10)), 2) // before the `\r`
    assertEquals(Positions.offset(s, Position(1, 1)), 5)
    assertEquals(Positions.offset(s, Position(7, 0)), s.content.length)
    assertEquals(Positions.offset(s, Position(-1, 3)), 0)
    assertEquals(Positions.position(s, 100), Position(1, 2))
  }

  test("ranges of spans") {
    val s = src("x.\nlonger : rel.")
    val r = Positions.range(Span(s, 3, 9))
    assertEquals((r.getStart, r.getEnd), (Position(1, 0), Position(1, 6)))
  }

class UrisSuite extends munit.FunSuite:
  test("file URIs map to paths and back") {
    val path = Uris.path("file:///tmp/a%20b/c.hgn")
    assertEquals(path, java.nio.file.Path.of("/tmp/a b/c.hgn").toString)
    assertEquals(Uris.uri(path).map(Uris.path), Some(path))
  }

  test("other URIs are kept as they are") {
    assertEquals(Uris.path("untitled:Untitled-1"), "untitled:Untitled-1")
    assertEquals(Uris.uri("untitled:Untitled-1"), Some("untitled:Untitled-1"))
  }

  test("the bundled standard library has no URI") {
    assertEquals(Uris.uri(hugin.compiler.SourceLoader.PreludePath), None)
  }
