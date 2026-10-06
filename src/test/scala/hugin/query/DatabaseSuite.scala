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

class DatabaseAccumulatorSuite extends munit.FunSuite:
  object Text extends Input[String, String]("text")
  object Notes extends Accumulator[String]("notes")

  /** Words of a text; notes every word longer than five characters. */
  object Words extends Query[String, Int]("words"):
    def compute(key: String)(using db: Database): Int =
      val ws = db.get(Text, key).split(" ").filter(_.nonEmpty)
      ws.filter(_.length > 5).foreach(w => db.push(Notes, s"$key: long word $w"))
      ws.length

  object Sum extends Query[List[String], Int]("sum"):
    def compute(keys: List[String])(using db: Database): Int =
      db.push(Notes, "sum")
      keys.map(db(Words, _)).sum

  test("accumulated values are collected along dependencies, each query once") {
    val db = Database()
    db.set(Text, "a", "a lengthy text")
    db.set(Text, "b", "short")
    assertEquals(db.accumulated(Notes, Sum, List("a", "b", "a")), Vector("a: long word lengthy", "sum"))
  }

  test("accumulated values are replaced on recomputation, also when the value cuts off") {
    val db = Database()
    db.set(Text, "a", "a lengthy text")
    db(Sum, List("a"))
    db.set(Text, "a", "a shorter word") // same number of words: `sum` is not recomputed
    db.stats.reset()
    assertEquals(db.accumulated(Notes, Sum, List("a")), Vector("a: long word shorter", "sum"))
    assertEquals(db.stats.computedBy("sum"), 0)
  }

  object Node extends Query[Int, String]("node"):
    /** 0 -> 1 -> 2 -> 0 with recovery: the re-entered query sees "?" and reports it. */
    def compute(n: Int)(using db: Database): String =
      val next = db(Node, (n + 1) % 3)
      s"$n($next)${if db.recoveredFromCycle then "!" else ""}"
    override def onCycle(n: Int): Option[String] = Some("?")

  object Outer extends Query[Unit, (String, Boolean)]("outer"):
    def compute(u: Unit)(using db: Database): (String, Boolean) =
      val v = db(Node, 0)
      (v, db.recoveredFromCycle)

  test("a cycle with a fallback is recovered; the flag stays inside the cycle") {
    val db = Database()
    val (v, outerRecovered) = db(Outer, ())
    assertEquals(v, "0(1(2(?)!)!)!")
    assert(!outerRecovered, "the query that demanded the cycle's head is not affected")
  }
