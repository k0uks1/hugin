package hugin.core

import CoreTesting.*

/** Literal and successor patterns split by value (issue #131, batch 2): coverage (E0911), unreachable
 *  clauses (W0006) and evaluation agree with the unary model, in which a numeral is `sucⁿ zero` and every
 *  pattern a constructor pattern. The model is evaluated directly: a clause matches a tuple of numerals
 *  by its literals and offsets, the first matching clause gives the value, and the numerals below the
 *  largest literal or offset plus two represent all (above them no pattern tells numerals apart). */
class NatPatternsSuite extends munit.FunSuite:
  /** A pattern of the model: a literal, `P + j` (`j = 0`: a variable or `_`). */
  private enum P:
    case Lit(k: Int)
    case Off(j: Int)
    def matches(v: Int): Boolean = this match
      case Lit(k) => v == k
      case Off(j) => v >= j

  /** A pattern as written: the forms that mean the same numeral are mixed in. */
  private def written(p: P, variable: String, rnd: scala.util.Random): String = p match
    case P.Lit(0) => if rnd.nextBoolean() then "0" else "zero"
    case P.Lit(k) => if rnd.nextInt(4) == 0 then s"(suc ${k - 1})" else k.toString
    case P.Off(0) => if rnd.nextBoolean() then "_" else variable
    case P.Off(j) =>
      // the successor written `a` times around `X + (j - a)`: the same pattern
      val a = rnd.nextInt(j + 1)
      val inner = if a == j then variable else s"($variable + ${j - a})"
      (1 to a).foldLeft(inner)((acc, _) => s"(suc $acc)")

  private val header = "nat : Type.\nzero : nat.\nsuc : nat -> nat.\n"

  test("value splits agree with the unary model on random programs (fixed seed)") {
    val rnd = scala.util.Random(131)
    for program <- 1 to 60 do
      val arity = 1 + rnd.nextInt(2)
      val clauses = List.fill(1 + rnd.nextInt(4)) {
        List.fill(arity) {
          rnd.nextInt(3) match
            case 0 => P.Lit(rnd.nextInt(7))
            case 1 => P.Off(1 + rnd.nextInt(3))
            case _ => P.Off(0)
        }
      }
      // the clauses on lines `first + i`, each with its own variable names
      val lines = clauses.zipWithIndex.map { (ps, i) =>
        val pats = ps.zipWithIndex.map((p, a) => written(p, s"X${a}c$i", rnd))
        s"f ${pats.mkString(" ")} = $i."
      }
      val sig = s"f : ${List.fill(arity)("nat").mkString(" -> ")} -> nat.\n"
      val source = header + sig + lines.mkString("\n") + "\n"
      val bound = 2 + clauses.flatten.map { case P.Lit(k) => k; case P.Off(j) => j }.max
      val tuples = (0 until arity).foldLeft(List(List.empty[Int]))((acc, _) => for t <- acc; v <- 0 until bound yield t :+ v)
      def first(t: List[Int]): Option[Int] = clauses.indexWhere(ps => ps.zip(t).forall((p, v) => p.matches(v))) match
        case -1 => None
        case i => Some(i)
      val e = elaborate(source)
      val covered = tuples.forall(first(_).isDefined)
      assertEquals(!e.errors.contains("E0911"), covered, s"coverage of\n$source\n${e.diagnostics.map(_.message)}")
      assert(e.errors.forall(_ == "E0911"), s"errors in\n$source\n${e.diagnostics.map(_.message)}")
      if covered then
        // (W0006 is reported for a function that covers its cases)
        val firstLine = header.count(_ == '\n') + 1
        val unreachable = e.diagnostics.filter(_.code.id == "W0006").map(_.primarySpan.startLine - firstLine).toSet
        val expected = clauses.indices.filterNot(i => tuples.exists(t => first(t).contains(i))).toSet
        assertEquals(unreachable, expected, s"unreachable clauses of\n$source")
        for t <- tuples do
          assertEquals(e.eval(s"f ${t.mkString(" ")}"), first(t).get.toString, s"f ${t.mkString(" ")} in\n$source")
  }

  test("offsets are converted by value: `suc (suc N)` is `N + 2`, `(N + 1) + 2` is `N + 3`") {
    val e = ok(
      header +
        """same : nat -> nat -> Type.
          |refl : same N N.
          |a : (n : nat) -> same (suc (suc n)) (n + 2) -> nat.
          |a _ refl = 0.
          |b : (n : nat) -> same (n + 2) (suc (suc n)) -> nat.
          |b _ refl = 0.
          |c : (n : nat) -> same ((n + 1) + 2) (n + 3) -> nat.
          |c _ refl = 0.
          |d : (n : nat) -> same (n + 100001) (suc (n + 100000)) -> nat.
          |d _ refl = 0.
          |e : (n : nat) -> same (n + 3) 5 -> nat.
          |e N refl = N.
          |""".stripMargin
    )
    assertEquals(e.eval("e 2 refl"), "2")
    assertEquals(e.eval("a 7 refl"), "0")
  }

  test("a literal pattern of any size is one test") {
    val e = ok(header + "f : nat -> nat.\nf 100000000000000000000 = 1.\nf (N + 100001) = 2.\nf _ = 0.\n")
    assertEquals(e.eval("f 100000000000000000000"), "1")
    assertEquals(e.eval("f 100000000000000000001"), "2")
    assertEquals(e.eval("f 100001"), "2")
    assertEquals(e.eval("f 100000"), "0")
  }
