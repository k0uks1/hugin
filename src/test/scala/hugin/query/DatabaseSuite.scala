package hugin.query

class DatabaseSuite extends munit.FunSuite:
  object Text extends Input[String, String]("text")

  object Length extends Query[String, Int]("length"):
    def compute(key: String)(using db: Database): Int = db.get(Text, key).length

  /** Parity of the length: a value that often stays the same (for early cut-off). */
  object Even extends Query[String, Boolean]("even"):
    def compute(key: String)(using db: Database): Boolean = db(Length, key) % 2 == 0

  object Report extends Query[String, String]("report"):
    def compute(key: String)(using db: Database): String = s"$key is ${if db(Even, key) then "even" else "odd"}"

  object Total extends Query[List[String], Int]("total"):
    def compute(keys: List[String])(using db: Database): Int = keys.map(db(Length, _)).sum

  object Loop extends Query[Int, Int]("loop"):
    def compute(n: Int)(using db: Database): Int = if n == 0 then db(Loop, 1) else db(Loop, 0)

  test("queries are memoised within a revision") {
    val db = Database()
    db.set(Text, "a", "hello")
    assertEquals(db(Report, "a"), "a is odd")
    assertEquals(db(Report, "a"), "a is odd")
    assertEquals(db.stats.computedBy("length"), 1)
    assertEquals(db.stats.computed, 3)
  }

  test("unrelated input changes revalidate without recomputing") {
    val db = Database()
    db.set(Text, "a", "hello")
    db.set(Text, "b", "x")
    db(Report, "a")
    db.stats.reset()
    db.set(Text, "b", "xy")
    assertEquals(db(Report, "a"), "a is odd")
    assertEquals(db.stats.computed, 0)
    assert(db.stats.reused > 0)
  }

  test("setting an equal value does not start a new revision") {
    val db = Database()
    db.set(Text, "a", "hello")
    val r = db.revision
    db.set(Text, "a", "hello")
    assertEquals(db.revision, r)
  }

  test("early cut-off: an unchanged intermediate result stops recomputation") {
    val db = Database()
    db.set(Text, "a", "hello")
    db(Report, "a")
    db.stats.reset()
    db.set(Text, "a", "world") // same length, so `length` is recomputed but `even` and `report` are not
    assertEquals(db(Report, "a"), "a is odd")
    assertEquals(db.stats.computedBy("length"), 1)
    assertEquals(db.stats.computedBy("even"), 0)
    assertEquals(db.stats.computedBy("report"), 0)
  }

  test("changes propagate to all dependents") {
    val db = Database()
    db.set(Text, "a", "hello")
    db.set(Text, "b", "x")
    assertEquals(db(Total, List("a", "b")), 6)
    db.set(Text, "b", "xyz")
    assertEquals(db(Total, List("a", "b")), 8)
    assertEquals(db(Report, "a"), "a is odd")
    db.set(Text, "a", "hell")
    assertEquals(db(Report, "a"), "a is even")
  }

  test("cycles are detected with the path of queries") {
    val db = Database()
    val e = intercept[CycleError](db(Loop, 0))
    assertEquals(e.path, List("loop(0)", "loop(1)", "loop(0)"))
  }

  test("missing and removed inputs") {
    val db = Database()
    intercept[MissingInput](db(Length, "nope"))
    db.set(Text, "a", "abc")
    assertEquals(db(Length, "a"), 3)
    db.remove(Text, "a")
    intercept[MissingInput](db(Length, "a"))
  }
