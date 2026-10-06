package hugin.compiler

import hugin.TestSupport

/** Resolution of import paths. */
class LibrariesSuite extends munit.FunSuite:
  test("resolve: relative to the importing file, `.hgn` appended without an extension") {
    assertEquals(SourceLoader.resolve("dir/main.hgn", "lib/geo"), "dir/lib/geo.hgn")
    assertEquals(SourceLoader.resolve("main.hgn", "geo.hgn"), "geo.hgn")
  }

  test("resolve: paths that are not file paths do not throw (found by the fuzzer, issue #7)") {
    assertEquals(SourceLoader.resolve("main.hgn", "a\u0000b"), "a\u0000b")
    assertEquals(SourceLoader.resolve("main.hgn", "/"), "/.hgn")
  }

  test("an import path with a NUL character is reported as missing") {
    val c = TestSupport.compile("m = %import \"a\\u{0}b\".")
    assertEquals(TestSupport.errorCodes(c), List("E0108"))
  }
