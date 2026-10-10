package hugin.query

/** After an edit of one item, every object item is revalidated (`ItemOf` executed and cut off, the item
 *  itself elaborated again): in time linear in the number of items (issue #126, PR 2), because
 *  `ObjectItems` is indexed by key and `ItemKey` caches its hash. */
class RevalidationSuite extends munit.FunSuite:
  private val path = "many.hgn"

  /** A program of `n` rules over a few declarations. */
  private def program(n: Int): String =
    "p : int -> rel.\nq : int -> int -> rel.\np 0.\n" + (1 to n).map(i => s"q $i X :- p X, X < $i.\n").mkString

  private val mx = java.lang.management.ManagementFactory.getThreadMXBean

  /** Edits one rule of a program of `n` rules: the CPU time (ns) of the compilation after the edit, and
   *  the executions of the item queries. */
  private def edit(n: Int, k: Int)(using db: Database): (Long, Int, Int) =
    val text = program(n)
    db.set(SourceText, path, text.replace(s"q ${n / 2} X :-", s"q ${n / 2} X :- X > $k,"))
    db.stats.reset()
    val c0 = mx.getCurrentThreadCpuTime
    db(ObjectItemsOf, ProgramKey(path, true))
    db(ElabProgram, ProgramKey(path, true))
    val t = mx.getCurrentThreadCpuTime - c0
    (t, db.stats.computedBy("itemOf"), db.stats.computedBy("elabItem"))

  private def setup(n: Int): Database =
    val db = Database()
    db.set(SourceText, path, program(n))
    db(ElabProgram, ProgramKey(path, true))
    db

  test("an edit of one rule revalidates every item once and elaborates one") {
    given db: Database = setup(400)
    val (_, itemOf, elabItem) = edit(400, 1)
    assertEquals(itemOf, 401) // the rules and the fact `p 0`, each cut off
    assertEquals(elabItem, 1)
  }

  test("revalidating after an edit is linear in the number of items") {
    def median(n: Int): Long =
      given db: Database = setup(n)
      val ts = (1 to 7).map(k => edit(n, k)._1).sorted
      ts(ts.length / 2)
    median(1000) // warm-up
    val small = median(1500)
    val large = median(6000)
    // four times the items: about four times the time when linear, sixteen times when quadratic
    assert(large < 9 * small, s"1500 items: ${small / 1e6} ms, 6000 items: ${large / 1e6} ms")
  }
