package hugin.query

import hugin.runtime.Reuse

/** An evaluation after a change of the rules copies the components before the first that changed from
 *  the earlier fixpoint (`hugin.runtime.Reuse`, issue #126, PR 4); its outcome is that of an evaluation
 *  from scratch, facts, answers and statistics alike. */
class ComponentReuseSuite extends munit.FunSuite:
  private val path = "reuse.hgn"
  private val facts = "reuse.facts"

  private val base =
    """edge : int -> int -> rel.
      |%input edge.
      |path : int -> int -> rel.
      |path X Y :- edge X Y.
      |path X Z :- path X Y, edge Y Z.
      |item : type.
      |box : int -> item.
      |boxed : item -> rel.
      |boxed (box X) :- edge X _.
      |""".stripMargin

  private val additions = List(
    "loop : int -> rel.\nloop X :- path X X.",
    "fan : int -> int -> rel.\nfan X N :- edge X _, N = count { Y | path X Y }.",
    "free : int -> rel.\nfree X :- edge X _, not path X 1.",
    "big : int -> rel.\nbig X :- boxed (box X), X > 2.",
    "path X Y :- edge Y X, X < 3.",
    "both : int -> rel.\nboth X :- loop X, big X.",
    "%output fan."
  )

  private val edges = (1 to 12).map(i => s"edge $i ${i % 7 + 1}.\nedge $i ${(i * 3) % 11 + 1}.").mkString("\n") + "\n"

  private def outcome(text: String, db: Database): (Option[List[String]], Option[List[String]], List[String]) =
    db.set(SourceText, path, text)
    db.set(SourceText, facts, edges)
    val o = db(Evaluate, EvaluateKey(CompileKey(path), List(facts)))
    (o.result.map(_.output), o.result.map(_.statistics), o.diagnostics.map(_.message))

  test("adding rules one by one: every evaluation equals one from scratch, and earlier components are copied") {
    val db = Database()
    var text = base + "?- path 1 X.\n"
    assert(outcome(text, db)._1.exists(_.nonEmpty))
    val before = Reuse.copied.get
    for a <- additions do
      text = text.replace("?- path 1 X.\n", s"$a\n?- path 1 X.\n")
      val incremental = outcome(text, db)
      assert(incremental._1.isDefined, s"$a: ${incremental._3}")
      assertEquals(incremental, outcome(text, Database()), a)
    assert(Reuse.copied.get - before >= additions.length, Reuse.copied.get - before)
  }

  test("the additions in other orders, and removals, equal evaluations from scratch") {
    val orders = List(additions.reverse.filterNot(_.startsWith("both")), additions.filterNot(_.startsWith("path")))
    for order <- orders do
      val db = Database()
      var parts = List.empty[String]
      outcome(base, db)
      for a <- order ++ order.reverse.drop(1) do
        parts = if parts.contains(a) then parts.filterNot(_ == a) else parts :+ a
        val text = base + parts.mkString("\n") + "\n?- edge X 2.\n"
        assertEquals(outcome(text, db), outcome(text, Database()), parts.mkString(" | "))
  }
