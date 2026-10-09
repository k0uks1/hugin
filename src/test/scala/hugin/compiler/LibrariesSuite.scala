package hugin.compiler

import hugin.TestSupport

/** Resolution of import paths. */
class LibrariesSuite extends munit.FunSuite:
  test("resolve: relative to the importing file, `.hgn` appended without an extension") {
    assertEquals(SourceLoader.resolve("dir/main.hgn", "lib/geo"), "dir/lib/geo.hgn")
    assertEquals(SourceLoader.resolve("main.hgn", "geo.hgn"), "geo.hgn")
  }

  test("resolve: `std/` denotes the bundled standard library, whatever the importing file") {
    assertEquals(SourceLoader.resolve("dir/main.hgn", "std/graph"), "<stdlib>/std/graph.hgn")
    assertEquals(SourceLoader.resolve("main.hgn", "std/graph.hgn"), "<stdlib>/std/graph.hgn")
    assertEquals(SourceLoader.resolve("<stdlib>/prelude.hgn", "std/list"), "<stdlib>/std/list.hgn")
    assertEquals(SourceLoader.resolve("dir/main.hgn", "std/./a/../graph"), "<stdlib>/std/graph.hgn")
    // a path that leaves `std/` is relative, as any other
    assertEquals(SourceLoader.resolve("dir/main.hgn", "std/../prelude"), "dir/prelude.hgn")
    assertEquals(SourceLoader.resolve("dir/main.hgn", "./std/graph"), "dir/std/graph.hgn")
  }

  test("a bundled `std/` module is imported and opened by `%use`") {
    assertEquals(TestSupport.run("%use \"std/testing_sample\".\nn : int -> rel.\nn (triple 2).\n%output n."), Right(List("n 6.")))
    // its `%export` hides `twice`
    val c = TestSupport.compile("s = %import \"std/testing_sample\".\nn : int -> rel.\nn (s.twice 2).")
    assertEquals(TestSupport.errorCodes(c), List("E0906"))
  }

  test("a missing `std/` module is E0108") {
    val c = TestSupport.compile("%use \"std/no_such_module\".")
    assertEquals(TestSupport.errorCodes(c), List("E0108"))
  }

  test("resolve: paths that are not file paths do not throw (found by the fuzzer, issue #7)") {
    assertEquals(SourceLoader.resolve("main.hgn", "a\u0000b"), "a\u0000b")
    assertEquals(SourceLoader.resolve("main.hgn", "/"), "/.hgn")
  }

  test("an import path with a NUL character is reported as missing") {
    val c = TestSupport.compile("m = %import \"a\\u{0}b\".")
    assertEquals(TestSupport.errorCodes(c), List("E0108"))
  }
