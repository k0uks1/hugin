package hugin.query

/** After an edit of one item, every object item is revalidated (`ItemOf` executed and cut off, the item
 *  itself elaborated again) with work linear in the number of items (issue #126, PR 2), because
 *  `ObjectItems` is indexed by key and `ItemKey` caches its hash. The work is counted, not timed. */
class RevalidationSuite extends munit.FunSuite:
  private val path = "many.hgn"

  /** A program of `n` rules over a few declarations. */
  private def program(n: Int): String =
    "p : int -> rel.\nq : int -> int -> rel.\np 0.\n" + (1 to n).map(i => s"q $i X :- p X, X < $i.\n").mkString

  /** Edits one rule of a program of `n` rules and elaborates it again: the executions of the item queries. */
  private def edit(n: Int, k: Int)(using db: Database): (Int, Int) =
    val text = program(n)
    db.set(SourceText, path, text.replace(s"q ${n / 2} X :-", s"q ${n / 2} X :- X > $k,"))
    db.stats.reset()
    db(ElabProgram, ProgramKey(path, true))
    (db.stats.computedBy("itemOf"), db.stats.computedBy("elabItem"))

  private def setup(n: Int): Database =
    val db = Database()
    db.set(SourceText, path, program(n))
    db(ElabProgram, ProgramKey(path, true))
    db

  test("an edit of one rule revalidates every item once and elaborates one") {
    given db: Database = setup(400)
    val (itemOf, elabItem) = edit(400, 1)
    assertEquals(itemOf, 401) // the rules and the fact `p 0`, each cut off
    assertEquals(elabItem, 1)
  }

  test("revalidating after an edit compares a bounded number of keys per item") {
    // the work counted, not timed: the comparisons of two keys' trees made while every item is
    // revalidated (a scan of the items per `ItemOf` made a number growing with the square of them)
    def comparisons(n: Int): Long =
      given db: Database = setup(n)
      val before = ItemKey.treeComparisons.get
      edit(n, 1)
      ItemKey.treeComparisons.get - before
    val (small, large) = (comparisons(1500), comparisons(6000))
    val counts = s"1500 items: $small comparisons, 6000 items: $large"
    assert(large <= 8L * 6000, counts)
    // four times the items, about four times the comparisons (a quadratic count would grow sixteenfold)
    assert(large <= 5 * small, counts)
  }
