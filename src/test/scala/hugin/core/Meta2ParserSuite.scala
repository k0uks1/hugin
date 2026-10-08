package hugin.core

import hugin.syntax.*
import hugin.util.*
import hugin.util.diagnostics.Code

/** The syntax of the new meta level (`meta2` parsing) and that the old syntax is unchanged. */
class Meta2ParserSuite extends munit.FunSuite:
  private def parse(code: String): (List[Item], List[Diagnostic]) =
    val r = Reporter()
    val p = Parser.parse(SourceFile.virtual("t.hgn", code), r)
    (p.items, r.diagnostics)

  private def show(code: String): String =
    val (items, diags) = parse(code)
    assert(diags.isEmpty, diags.map(_.message).mkString("\n"))
    items.map(Printer.showItem).mkString("\n")

  test("clauses with constructor patterns") {
    assertEquals(show("plus (suc M) N = suc (plus M N)."), "plus (suc M) N = suc (plus M N).")
    assert(parse("plus (suc M) N = suc (plus M N).")._1.head.isInstanceOf[Clause])
    // all-variable heads stay definitions
    assert(parse("f X Y = X.")._1.head.isInstanceOf[Def])
  }

  test("implicit Π types") {
    assertEquals(show("id : {A : Type} -> A -> A."), "id : {A : Type} -> (A -> A).")
    assertEquals(show("k : {A B : Type} -> A -> B -> A."), "k : {A B : Type} -> (A -> (B -> A)).")
    assertEquals(show("f : {x : nat} -> nat."), "f : {x : nat} -> nat.")
  }

  test("splices and lifts") {
    assertEquals(show("p X :- q $X."), "p X :- q $X.")
    assertEquals(show("c : ⇑node = a."), "c : ⇑node = a.")
  }

  test("where blocks: layout by column") {
    val (items, diags) = parse("""f (c X) = y
                                 |  where y = z.
                                 |        z = X.
                                 |g = 1.
                                 |""".stripMargin)
    assert(diags.isEmpty, diags.map(_.message).mkString)
    assertEquals(items.length, 2)
    items.head match
      case Clause(_, _, where) => assertEquals(where.length, 2)
      case other => fail(s"expected a clause, got $other")
  }

  test("nested where blocks are relative to their binding's column") {
    val (items, diags) = parse("""f X = a
                                 |  where a = b
                                 |          where b = X.
                                 |        c = a.
                                 |""".stripMargin)
    assert(diags.isEmpty, diags.map(_.message).mkString)
    items.head match
      case Clause(_, _, List(Clause(_, _, inner), _)) => assertEquals(inner.length, 1)
      case other => fail(s"unexpected $other")
  }
