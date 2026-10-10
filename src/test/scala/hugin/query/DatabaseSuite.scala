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

  /** Whether `body` was cancelled ([[Cancelled]] is a control throwable, which `intercept` passes on). */
  private def cancelled(body: => Any): Boolean =
    try
      body
      false
    catch case _: Cancelled => true

  test("a cancelled computation stores no memo of the queries it unwinds; completed ones stay valid") {
    val db = Database()
    db.set(Text, "a", "hello")
    db.set(Text, "b", "xy")
    // `Total` demands `Length a`, then `Length b`; the computation is cancelled after the first
    var cancel = false
    db.cancellation = () => cancel
    object Watch extends Query[String, Int]("watch"):
      def compute(key: String)(using db: Database): Int =
        val n = db(Length, key)
        cancel = true
        n
    object Both extends Query[Unit, Int]("both"):
      def compute(key: Unit)(using db: Database): Int = db(Watch, "a") + db(Length, "b")
    assert(cancelled(db(Both, ())))
    assertEquals(db.memoCount(Both), 0)
    assertEquals(db.memoCount(Watch), 1) // completed before the check that failed
    assertEquals(db.memoCount(Length), 1) // `Length b` was not computed
    // the database is consistent: once no longer cancelled, the result equals one from scratch and
    // only the unwound query and what it had not reached are computed
    cancel = false
    db.cancellation = Database.neverCancelled
    db.stats.reset()
    assertEquals(db(Both, ()), 7)
    assertEquals(db.stats.computedBy.toMap, Map("both" -> 1, "length" -> 1))
    // a cancelled recomputation keeps the earlier memo, which is verified again on the next demand
    db.set(Text, "b", "xyz")
    db.cancellation = () => true
    assert(cancelled(db(Both, ())))
    db.cancellation = Database.neverCancelled
    assertEquals(db(Both, ()), 8)
  }

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

  test("a removed input read again from its default invalidates the results of its old value") {
    var disk = "one"
    object File extends Input[String, String]("file"):
      override def default(key: String): Option[String] = Some(disk)
    object Size extends Query[String, Int]("size"):
      def compute(key: String)(using db: Database): Int = db.get(File, key).length
    object Both extends Query[String, Int]("both"):
      def compute(key: String)(using db: Database): Int = if db.has(File, key) then db(Size, key) else 0
    val db = Database()
    assertEquals(db(Both, "f"), 3)
    disk = "three"
    db.remove(File, "f")
    // `both` reads the default again (through `has`) before `size` is verified
    assertEquals(db(Both, "f"), 5)
  }

  // --------------------------------------------------------------------------------------- eviction

  /** The words of a text, each measured by its own query (keys that come and go with edits). */
  object Words extends Query[String, Int]("words"):
    def compute(key: String)(using db: Database): Int = db.get(Text, key).split(' ').toList.map(w => db(Word, w)).sum
  object Word extends Query[String, Int]("word"):
    def compute(w: String)(using db: Database): Int = w.length

  test("collection drops the memos of keys that are no longer reached, and keeps the others") {
    val db = Database(retainEpochs = 1, collectAbove = Int.MaxValue)
    db.set(Text, "a", "one two three")
    assertEquals(db(Words, "a"), 11)
    assertEquals(db.memoCount, 4)
    db.set(Text, "a", "one two four")
    assertEquals(db(Words, "a"), 10)
    assertEquals(db.memoCount, 5)
    assertEquals(db.collect(), 1) // `three`
    assertEquals(db.memoCount, 4)
    db.stats.reset()
    assertEquals(db(Words, "a"), 10)
    assertEquals(db.stats.computed, 0)
  }

  test("collection keeps what the last epochs demanded; dropped results are computed again") {
    val db = Database(retainEpochs = 2, collectAbove = Int.MaxValue)
    db.set(Text, "a", "x y")
    db.set(Text, "b", "z")
    db(Words, "a")
    db.set(Text, "c", "w") // a new revision, and epoch: `b` is demanded
    db(Words, "b")
    assertEquals(db.collect(), 0) // both epochs are retained
    db.set(Text, "c", "v")
    db(Words, "b")
    assertEquals(db.collect(), 3) // `a` was demanded three epochs ago: `words(a)`, `word(x)`, `word(y)`
    db.stats.reset()
    assertEquals(db(Words, "a"), 2)
    assertEquals(db.stats.computedBy("words"), 1)
    assertEquals(db(Words, "b"), 1)
  }

  test("collections run automatically and keep the number of memos bounded") {
    val db = Database(collectAbove = 16)
    val rnd = scala.util.Random(7)
    var max = 0
    for i <- 1 to 300 do
      db.set(Text, "a", List.fill(5)(rnd.nextInt(1000).toString).mkString(" "))
      db(Words, "a")
      max = max.max(db.memoCount)
    assert(db.stats.collections > 0)
    assert(max <= 3 * 16, s"up to $max memos")
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
