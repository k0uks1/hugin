package hugin.runtime

import hugin.TestSupport
import org.scalacheck.{Gen, Prop}

/** Differential tests of the semi-naive engine against reference computations in Scala. */
class EngineSuite extends munit.ScalaCheckSuite:
  override def scalaCheckTestParameters = super.scalaCheckTestParameters.withMinSuccessfulTests(30)

  private val graphs: Gen[Set[(Int, Int)]] =
    for
      n <- Gen.choose(1, 12)
      m <- Gen.choose(0, 3 * n)
      edges <- Gen.listOfN(m, Gen.zip(Gen.choose(0, n - 1), Gen.choose(0, n - 1)))
    yield edges.toSet

  private val tc = """
    edge : int -> int -> rel.
    %input edge.
    path : int -> int -> rel.
    path X Y :- edge X Y.
    path X Z :- path X Y, path Y Z.
    %output path.
  """

  private def reference(edges: Set[(Int, Int)]): Set[(Int, Int)] =
    var closure = edges
    var changed = true
    while changed do
      val next = closure ++ (for (a, b) <- closure; (c, d) <- closure if b == c yield (a, d))
      changed = next.size != closure.size
      closure = next
    closure

  property("transitive closure (non-linear recursion) agrees with a naive fixpoint") {
    Prop.forAll(graphs) { edges =>
      val facts = edges.map((a, b) => s"edge $a $b.").mkString("\n")
      val expected = reference(edges).map((a, b) => s"path $a $b.").toList.sorted
      assertEquals(TestSupport.run(tc, facts), Right(expected))
    }
  }

  test("interning: equal nested facts have one identity (A.2 (2))") {
    val out = TestSupport.run("""
      w : type. mk : int -> w.
      s : int -> int -> rel. s 1 2. s 1 3.
      g : w -> rel. g (mk X) :- s X _.
      n : int -> rel. n N :- N = count { M | M = mk 1 }.
      %output n.
    """)
    assertEquals(out, Right(List("n 1.")))
  }

  test("%partial is removed: a program that cannot be shown to terminate is rejected") {
    val prog = "nat : int -> rel. nat 0. nat M :- nat N, M = N + 1. %output nat."
    assertEquals(TestSupport.run(prog), Left(List("E0603")))
    assertEquals(TestSupport.run("nat : int -> rel. %partial nat."), Left(List("E0001")))
  }

  test("aggregates count distinct bindings and sum of nothing is 0 (Definition 8.4)") {
    val out = TestSupport.run("""
      p : int -> int -> rel. p 1 5. p 2 5. p 3 7.
      c : int -> rel. c N :- N = count { X | p X _ }.
      s : int -> rel. s N :- N = sum { V | p _ V }.
      z : int -> rel. z N :- N = sum { V | p 9 V }.
      %output c. %output s. %output z.
    """)
    // the wildcard is a variable of the aggregate: three distinct bindings (1,5) (2,5) (3,7)
    assertEquals(out, Right(List("c 3.", "s 17.", "z 0.")))
  }
