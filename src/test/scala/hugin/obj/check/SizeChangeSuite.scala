package hugin.obj
package check

import hugin.TestSupport
import hugin.fuzz.Fuzz
import org.scalacheck.{Gen, Prop}

/** The termination check is sound on random integer recursion (reference: object/termination): every program it
 *  accepts — by descent along derivations (A) or by guarded induction (B) with an inferred measure —
 *  reaches its fixed point. Rules permute, shift and halve the arguments of one or two mutually recursive
 *  relations under random guards, so many are rejected, and the accepted ones cover both directions. */
class SizeChangeSuite extends munit.ScalaCheckSuite:
  override def scalaCheckTestParameters =
    super.scalaCheckTestParameters.withMinSuccessfulTests(Fuzz.count.getOrElse(300)).withWorkers(1)

  private val program = SizeChangePrograms.program()

  property("an accepted program reaches its fixed point") {
    Prop.forAll(program) { code =>
      val c = TestSupport.compile(code)
      if c.reporter.hasErrors then Prop.collect("rejected")(Prop.passed)
      else
        Fuzz.guarded(TestSupport.run(code)) match
          case Right(Right(_)) => Prop.collect("accepted")(Prop.passed)
          case Right(Left(codes)) => Prop.falsified :| s"accepted, but the run failed with $codes\n$code"
          case Left(f) => Prop.falsified :| s"accepted, but ${f.describe}\n$code"
    }
  }

/** Random integer recursion for [[SizeChangeSuite]] and [[ClosureCrossCheckSuite]]. */
object SizeChangePrograms:
  private def expr(vars: List[String]): Gen[String] = Gen.frequency(
    3 -> Gen.oneOf(vars),
    3 -> Gen.zip(Gen.oneOf(vars), Gen.oneOf("+", "-"), Gen.choose(1, 2)).map((v, op, k) => s"$v $op $k"),
    1 -> Gen.oneOf(vars).map(v => s"$v / 2"),
    1 -> Gen.choose(0, 3).map(_.toString)
  )

  private def guard(vars: List[String]): Gen[String] =
    Gen.zip(Gen.oneOf(vars), Gen.oneOf(">", ">=", "<", "<="), Gen.choose(-2, 12)).map((v, op, c) => s"$v $op $c")

  private def rule(head: String, body: String): Gen[String] =
    for
      e1 <- expr(List("X", "Y"))
      e2 <- expr(List("X", "Y"))
      n <- Gen.choose(0, 2)
      gs <- Gen.listOfN(n, guard(List("X", "Y", "A", "B")))
    yield (s"$head A B :- $body X Y" :: gs ++ List(s"A = $e1", s"B = $e2")).mkString("", ", ", ".")

  /** One relation or two mutually recursive ones, with 1 to `maxRules` rules (`three`: up to three relations
   *  calling each other arbitrarily, for larger closures). */
  def program(maxRules: Int = 3, three: Boolean = false): Gen[String] =
    val rels = if three then List("p", "q", "r") else List("p", "q")
    for
      mutual <- Gen.oneOf(true, false)
      n <- Gen.choose(1, maxRules)
      pairs =
        if three then for h <- rels; b <- rels yield (h, b)
        else if mutual then List(("p", "q"), ("q", "p"))
        else List(("p", "p"))
      rules <- Gen.listOfN(n, Gen.oneOf(pairs).flatMap((h, b) => rule(h, b)))
      facts <- Gen.listOfN(2, Gen.zip(Gen.choose(0, 9), Gen.choose(0, 9))).map(_.map((a, b) => s"p $a $b."))
    yield (rels.map(r => s"$r : int -> int -> rel.") ++ facts ++ rules ++ rels.map(r => s"%output $r.")).mkString("\n")
