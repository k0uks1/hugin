package hugin.fuzz

import hugin.syntax.{Lexer, Tok}
import hugin.util.{Reporter, SourceFile}
import org.scalacheck.{Gen, Shrink}

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** The seed corpus: the `.hgn` files under `examples` and `tests`, with their `.facts` files. Programs in
 *  the syntax of the new meta level (run with `--new-meta`, see their `.flags`) are not part of it: the
 *  compiler pipeline does not accept that syntax yet. */
object Corpus:
  final case class Entry(path: String, program: Program)

  val entries: Vector[Entry] =
    val roots = List(Path.of("examples"), Path.of("tests"))
    roots
      .flatMap(r => Files.walk(r).iterator().asScala.filter(_.toString.endsWith(".hgn")))
      .filterNot(newMeta)
      .sortBy(_.toString)
      .map { p =>
        val facts = Path.of(p.toString.stripSuffix(".hgn") + ".facts")
        val program = Program(Files.readString(p), Option.when(Files.exists(facts))(Files.readString(facts)), p.getParent.toString)
        Entry(p.toString, program)
      }
      .toVector

  private def newMeta(p: Path): Boolean =
    val flags = Path.of(p.toString.stripSuffix(".hgn") + ".flags")
    Files.exists(flags) && Files.readString(flags).contains("--new-meta")

/** A token of a mutated program together with the layout (white space, comments) before it. */
final case class Piece(gap: String, text: String, kind: Tok = Tok.Error):
  def code: String = gap + text

/** A mutated program as a token sequence; the last piece is the trailing layout. Shrinking removes tokens. */
final case class Mutant(origin: String, dir: String, pieces: Vector[Piece], facts: Option[String]):
  def program: Program = Program(pieces.map(_.code).mkString, facts, dir)
  override def toString: String = s"mutant of $origin:$program"

object Mutant:
  def tokenize(code: String): Vector[Piece] =
    val toks = Lexer(SourceFile.virtual("mutant.hgn", code), Reporter()).tokenize()
    val ends = 0 +: toks.map(_.span.end)
    toks.zip(ends).map((t, prev) => Piece(code.substring(prev, t.span.start), t.text, t.kind))

  /** Token-level shrinking: ScalaCheck's container shrink removes chunks of tokens, tokens stay intact. */
  given Shrink[Mutant] = Shrink { m =>
    given Shrink[Piece] = Shrink.shrinkAny
    Shrink.shrink(m.pieces.init).map(ps => m.copy(pieces = ps :+ m.pieces.last))
  }

/** Token-, kind- and line-level mutations of corpus programs. */
object Mutations:
  /** Tokens that are likely to confuse the lexer, the parser's recovery or import resolution. */
  private val special: Vector[String] = Vector(
    "%import",
    "\"/\"",
    "\"..\"",
    "\"\\u{0}\"",
    "(*",
    "*)",
    "\"",
    "\"\\u{110000}\"",
    "\"\\q\"",
    "9223372036854775808",
    "-9223372036854775808",
    "99999999999999999999",
    "1.5e",
    "%",
    "@",
    "%complete",
    "%infix left 5 op",
    "..",
    "{",
    "}",
    "(",
    ")",
    "[",
    "]",
    ".",
    ",",
    ";",
    ":-",
    "?-",
    ":",
    "<:",
    "|",
    "_",
    "é",
    "\t",
    "\u0000",
    "with",
    "as",
    "not",
    "~",
    "'"
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

  /** Literals that probe the bounds of the lexer, constant folding and the primitives. */
  private val literals: Vector[String] = Vector(
    "0",
    "-1",
    "9223372036854775807",
    "9223372036854775808",
    "-9223372036854775808",
    "1.0e308",
    "1.0e309",
    "0.0",
    "-0.0",
    "\"\"",
    "\"\\u{1F600}\"",
    "\"\\u{D800}\"",
    "\"a\\nb\"",
    "\"" + "x" * 300 + "\""
  )

  private val brackets: Vector[String] = Vector("(", ")", "{", "}", "[", "]")

  /** Mutations aimed at a kind of token: renaming an identifier everywhere (to another one of the corpus
   *  or a fresh one), removing a period, damaging brackets, changing a literal. */
  private def targetedMutation(m: Mutant): Gen[Mutant] =
    val ps = m.pieces
    def at(p: Piece => Boolean): Vector[Int] = ps.indices.filter(i => p(ps(i))).toVector
    def onePiece(is: Vector[Int])(f: Int => Gen[Vector[Piece]]): Option[Gen[Mutant]] =
      Option.when(is.nonEmpty)(Gen.oneOf(is).flatMap(f).map(p => m.copy(pieces = p)))
    val idents = at(p => p.kind == Tok.Name || p.kind == Tok.Var)
    val rename = onePiece(idents) { i =>
      val old = ps(i)
      val sameKind = vocabulary.filter(t => t.nonEmpty && t.head.isUpper == old.text.head.isUpper && t.head.isLetter)
      Gen.oneOf(Gen.oneOf(sameKind), Gen.const(old.text + "'"), Gen.const(old.text + "_x")).map { name =>
        ps.map(p => if p.kind == old.kind && p.text == old.text then p.copy(text = name) else p)
      }
    }
    val period = onePiece(at(_.kind == Tok.Period))(i => Gen.const(ps.patch(i, Nil, 1)))
    val brace = onePiece(at(p => brackets.contains(p.text))) { i =>
      Gen.oneOf(
        Gen.const(ps.patch(i, Nil, 1)), // unbalance
        Gen.oneOf(brackets).map(b => ps.updated(i, ps(i).copy(text = b))) // mismatch
      )
    }
    val literal = onePiece(at(p => p.kind == Tok.IntLit || p.kind == Tok.FloatLit || p.kind == Tok.StrLit)) { i =>
      Gen.oneOf(literals).map(l => ps.updated(i, ps(i).copy(text = l)))
    }
    val choices = List(rename, period, brace, literal).flatten
    if choices.isEmpty then tokenMutation(m) else Gen.oneOf(choices).flatMap(identity)

  private def lineMutation(m: Mutant): Gen[Mutant] =
    val code = m.pieces.map(_.code).mkString
    val lines = code.split("\n", -1).toVector
    val mutated =
      for
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
    else Gen.frequency(4 -> tokenMutation(m), 3 -> targetedMutation(m), 1 -> lineMutation(m)).flatMap(mutate(_, n - 1))

  /** One to four mutations of a corpus program. */
  val mutants: Gen[Mutant] =
    for
      e <- Gen.oneOf(Corpus.entries)
      n <- Gen.choose(1, 4)
      m <- mutate(Mutant(e.path, e.program.dir, Mutant.tokenize(e.program.code), e.program.facts), n)
    yield m
