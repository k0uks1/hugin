package hugin.util

import hugin.syntax.Literal
import org.scalacheck.{Gen, Prop}
import scala.util.hashing.MurmurHash3

/** [[Levenshtein]] replaced commons-text's `LevenshteinDistance` (issue #58) and gives the same distances,
 *  so the suggestions are the same; `Literal.quote` no longer uses `String.codePoints`. */
class LevenshteinSuite extends munit.ScalaCheckSuite:
  private val alphabet = "abcAB_é😀𐀀\n\t\"\\\u0001\u007f".toVector

  test("distances are those of commons-text's LevenshteinDistance") {
    // the fingerprint was recorded from commons-text 1.12.0 on the same strings
    val rnd = scala.util.Random(63)
    def str() = String(Array.fill(rnd.nextInt(9))(alphabet(rnd.nextInt(alphabet.length))))
    val distances = List.fill(50000)(Levenshtein.distance(str(), str()))
    assertEquals(MurmurHash3.orderedHash(distances), 1579951138)
  }

  test("examples") {
    assertEquals(Levenshtein.distance("kitten", "sitting"), 3)
    assertEquals(Levenshtein.distance("", "abc"), 3)
    assertEquals(Levenshtein.distance("abc", ""), 3)
    assertEquals(Levenshtein.distance("edge", "edge"), 0)
    assertEquals(Levenshtein.distance("ab", "ba"), 2) // no transpositions
    assertEquals(Levenshtein.distance("a", "😀"), 2) // UTF-16 code units
  }

  /** The definition, by recursion on both strings. */
  private def naive(a: String, b: String): Int =
    if a.isEmpty then b.length
    else if b.isEmpty then a.length
    else
      val cost = if a.head == b.head then 0 else 1
      (naive(a.tail, b) + 1).min(naive(a, b.tail) + 1).min(naive(a.tail, b.tail) + cost)

  property("the distance is the definition's, and symmetric") {
    val strings = Gen.listOfN(5, Gen.oneOf(alphabet)).flatMap(cs => Gen.choose(0, 5).map(n => cs.take(n).mkString))
    Prop.forAll(strings, strings)((a, b) => Levenshtein.distance(a, b) == naive(a, b) && Levenshtein.distance(b, a) == naive(a, b))
  }

  test("quoting goes by code points, an unpaired surrogate is one") {
    assertEquals(Literal.quote("a\"b\\c\nd\te"), "\"a\\\"b\\\\c\\nd\\te\"")
    assertEquals(Literal.quote("\u0001\u007f\u001f"), "\"\\u{1}\\u{7f}\\u{1f}\"")
    assertEquals(Literal.quote("😀\ud800x\udc00"), "\"😀\ud800x\udc00\"")
    assertEquals(Literal.quote("\ud83d"), "\"\ud83d\"")
  }
