package hugin.fuzz

import hugin.syntax.Lexer
import hugin.util.{Reporter, SourceFile}
import org.scalacheck.{Gen, Shrink}

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** The seed corpus: the `.hgn` files under `examples` and `tests`, with their `.facts` files. */
object Corpus:
  final case class Entry(path: String, program: Program)

  val entries: Vector[Entry] =
    val roots = List(Path.of("examples"), Path.of("tests"))
    roots
      .flatMap(r => Files.walk(r).iterator().asScala.filter(_.toString.endsWith(".hgn")))
      .sortBy(_.toString)
      .map { p =>
        val facts = Path.of(p.toString.stripSuffix(".hgn") + ".facts")
        Entry(p.toString, Program(Files.readString(p), Option.when(Files.exists(facts))(Files.readString(facts))))
      }
      .toVector

/** A token of a mutated program together with the layout (white space, comments) before it. */
final case class Piece(gap: String, text: String):
  def code: String = gap + text

/** A mutated program as a token sequence; the last piece is the trailing layout. Shrinking removes tokens. */
final case class Mutant(origin: String, pieces: Vector[Piece], facts: Option[String]):
  def program: Program = Program(pieces.map(_.code).mkString, facts)
  override def toString: String = s"mutant of $origin:$program"

object Mutant:
  def tokenize(code: String): Vector[Piece] =
    val toks = Lexer(SourceFile.virtual("mutant.hgn", code), Reporter()).tokenize()
    val ends = 0 +: toks.map(_.span.end)
    toks.zip(ends).map((t, prev) => Piece(code.substring(prev, t.span.start), t.text))

  /** Token-level shrinking: ScalaCheck's container shrink removes chunks of tokens, tokens stay intact. */
  given Shrink[Mutant] = Shrink { m =>
    given Shrink[Piece] = Shrink.shrinkAny
    Shrink.shrink(m.pieces.init).map(ps => m.copy(pieces = ps :+ m.pieces.last))
  }

/** Token- and line-level mutations of corpus programs. */
object Mutations:
  /** Tokens that are likely to confuse the lexer or the parser's recovery. */
  private val special: Vector[String] = Vector(
    "(*", "*)", "\"", "\"\\u{110000}\"", "\"\\q\"", "9223372036854775808", "-9223372036854775808", "99999999999999999999",
    "1.5e", "%", "@", "%complete", "%infix left 5 op", "..", "{", "}", "(", ")", "[", "]", ".", ",", ";", ":-", "?-", ":",
    "<:", "|", "_", "é", "\t", "\u0000", "with", "as", "not", "~", "'"
  )

  private lazy val vocabulary: Vector[String] =
    Corpus.entries.flatMap(e => Mutant.tokenize(e.program.code).map(_.text)).filter(_.nonEmpty).distinct.sorted

  private val token: Gen[String] = Gen.frequency(3 -> Gen.oneOf(vocabulary), 1 -> Gen.oneOf(special))

  private def tokenMutation(m: Mutant): Gen[Mutant] =
    val ps = m.pieces
    val n = ps.length - 1 // the trailing layout stays last
    if n == 0 then token.map(t => m.copy(pieces = Piece("", t) +: ps))
    else
      Gen.choose(0, n - 1).flatMap { i =>
        Gen.oneOf(
          Gen.const(ps.patch(i, Nil, 1)), // delete
          Gen.const(ps.patch(i, List(ps(i), ps(i)), 1)), // duplicate
          Gen.const(if i + 1 < n then ps.patch(i, List(ps(i + 1), ps(i)), 2) else ps), // swap with the next token
          token.map(t => ps.updated(i, ps(i).copy(text = t))), // replace
          token.map(t => ps.patch(i, List(Piece(" ", t)), 0)) // insert
        ).map(p => m.copy(pieces = p))
      }

  private def lineMutation(m: Mutant): Gen[Mutant] =
    val code = m.pieces.map(_.code).mkString
    val lines = code.split("\n", -1).toVector
    val mutated = for
      i <- Gen.choose(0, lines.length - 1)
      j <- Gen.choose(0, lines.length - 1)
      ls <- Gen.oneOf(
        lines.patch(i, Nil, 1), // delete a line
        lines.patch(i, List(lines(i), lines(i)), 0), // duplicate a line
        lines.updated(i, lines(j)).updated(j, lines(i)), // swap two lines
        lines.patch(i, Nil, 1).patch(j.min(lines.length - 1), List(lines(i)), 0), // move a line
        lines.take(i) :+ lines(i).take(lines(i).length / 2) // truncate the file
      )
    yield ls.mkString("\n")
    mutated.map(c => m.copy(pieces = Mutant.tokenize(c)))

  private def mutate(m: Mutant, n: Int): Gen[Mutant] =
    if n == 0 then Gen.const(m)
    else Gen.frequency(4 -> tokenMutation(m), 1 -> lineMutation(m)).flatMap(mutate(_, n - 1))

  /** One to four mutations of a corpus program. */
  val mutants: Gen[Mutant] =
    for
      e <- Gen.oneOf(Corpus.entries)
      n <- Gen.choose(1, 4)
      m <- mutate(Mutant(e.path, Mutant.tokenize(e.program.code), e.program.facts), n)
    yield m
