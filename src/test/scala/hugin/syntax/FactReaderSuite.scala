package hugin.syntax

import hugin.util.*
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** The fact reader against the program parser (issue #60): wherever the reader accepts a file, the parser
 *  parses it without diagnostics into the same trees with the same spans. On the facts files of the tests
 *  and the bench set, on the goldens' programs (which the reader rejects), and on mutated and generated
 *  facts files. */
class FactReaderSuite extends munit.FunSuite:
  /** A tree with every span, as text. */
  private def dump(x: Any, sb: StringBuilder): Unit = x match
    case t: (Tree | Trees.Item) =>
      val p = t.asInstanceOf[Product]
      val span = t match
        case t: Tree => t.span
        case i: Trees.Item => i.span
      sb ++= p.productPrefix += '@' ++= span.start.toString += '-' ++= span.end.toString += '('
      p.productIterator.foreach { c =>
        dump(c, sb); sb += ','
      }
      sb += ')'
    case it: Iterable[?] =>
      sb += '[';
      it.foreach { c =>
        dump(c, sb); sb += ','
      }; sb += ']'
    case p: Product =>
      sb ++= p.productPrefix += '(';
      p.productIterator.foreach { c =>
        dump(c, sb); sb += ','
      }; sb += ')'
    case o => sb ++= o.toString

  private def text(items: List[Trees.Item]): String =
    val sb = StringBuilder()
    items.foreach { i =>
      dump(i, sb); sb += '\n'
    }
    sb.toString

  /** Whether the reader accepted `content`; if it did, the parser agrees. */
  private def agrees(path: String, content: String): Boolean =
    val src = SourceFile.virtual(path, content)
    FactReader.read(src) match
      case None => false
      case Some(items) =>
        val reporter = Reporter()
        val parsed = Parser.parse(SourceFile.virtual(path, content), reporter)
        assertEquals(reporter.diagnostics.map(_.message.toString), Nil, s"$path:\n$content")
        assertEquals(text(items), text(parsed.items), s"$path:\n$content")
        true

  private def files(ext: String): List[Path] =
    List("tests", "bench", "examples").map(Path.of(_)).flatMap(d => Files.walk(d).iterator.asScala.filter(_.toString.endsWith(ext)).toList)
      .sortBy(_.toString)

  test("the facts files of the tests and the bench set are read as the parser parses them") {
    val accepted = files(".facts").filter(f => agrees(f.toString, Files.readString(f)))
    // the bench set's (the large ones) are in the common form; some tests' files have errors on purpose
    for f <- files(".facts") if f.startsWith("bench") do assert(accepted.contains(f), s"$f not in the common form")
    assert(accepted.length >= files(".facts").length / 2, accepted.toString)
  }

  test("programs are not facts files: the reader leaves them to the parser") {
    val programs = files(".hgn")
    assert(programs.count(f => agrees(f.toString, Files.readString(f))) < programs.length / 20)
  }

  private val samples = List(
    "edge 1 2.\nedge 2 3.\n",
    "p (-3) (-2.5) \"a\\\"b\\n\" x 1e309.\n",
    "  p 1.  p 2. (* comment *) p 3.\n",
    "p (c 1 (d 2 x)) (e).\n",
    "p\n  1\n  2.\n",
    "p 1\n2.\n", // a token in column 0: the parser reports the missing period
    "p (\n3).\n",
    "p 1 2\n.\n",
    "p (- 9223372036854775808).\n",
    "p 9223372036854775808.\n",
    "p (1 2).\n",
    "p ((x)).\n",
    "p (-x).\n",
    "p X _.\n",
    "p a.b.\n",
    "%infix left 5 x.\np 1 x 2.\n",
    "p 1 + 2.\n",
    "p 1, q 2.\n",
    "p (1.\n",
    "p \"unterminated.\n",
    "(* open comment\np 1.\n",
    "p 1 :- q 1.\n",
    "@r p 1.\n",
    "p 1. q.\n",
    ""
  )

  test("hand-written cases: accepted ones agree with the parser, the rest are left to it") {
    val accepted = samples.count(s => agrees("s.facts", s))
    assert(accepted >= 6 && accepted < samples.length, s"$accepted accepted")
  }

  test("mutated facts files: wherever the reader accepts one, the parser agrees") {
    val rnd = scala.util.Random(60)
    val corpus = samples ++ files(".facts").map(f => Files.readString(f).take(3000))
    val pieces = List(
      "(",
      ")",
      "-",
      ".",
      " ",
      "\n",
      "\n ",
      "x",
      "X",
      "1",
      "2.5",
      "\"s\"",
      "(*",
      "*)",
      ",",
      ":-",
      "%",
      "@",
      "_",
      "9223372036854775808",
      "\\"
    )
    var accepted = 0
    var rejected = 0
    for _ <- 0 until 3000 do
      val base = corpus(rnd.nextInt(corpus.length))
      var t = base
      for _ <- 0 to rnd.nextInt(3) do
        val k = if t.isEmpty then 0 else rnd.nextInt(t.length)
        t = rnd.nextInt(3) match
          case 0 if t.nonEmpty => t.patch(k, "", (1 + rnd.nextInt(3)).min(t.length - k))
          case 1 => t.patch(k, pieces(rnd.nextInt(pieces.length)), 0)
          case _ => t.patch(k, pieces(rnd.nextInt(pieces.length)), 1.min(t.length - k))
      if agrees("m.facts", t) then accepted += 1 else rejected += 1
    assert(accepted > 300 && rejected > 300, s"accepted $accepted, rejected $rejected")
  }

  test("generated facts files with nested terms, negative numbers, strings and layout") {
    val rnd = scala.util.Random(61)
    def term(depth: Int): String = rnd.nextInt(if depth > 2 then 5 else 7) match
      case 0 => rnd.nextInt(1000).toString
      case 1 => s"(-${rnd.nextInt(1000)})"
      case 2 => f"${rnd.nextDouble() * 100}%.3f"
      case 3 => "\"" + rnd.alphanumeric.take(rnd.nextInt(5)).mkString + (if rnd.nextBoolean() then "\\t" else "") + "\""
      case 4 => List("a", "bc", "node_1")(rnd.nextInt(3))
      case _ => s"(c${rnd.nextInt(3)}" + (0 until 1 + rnd.nextInt(3)).map(_ => " " + term(depth + 1)).mkString + ")"
    def space(): String = rnd.nextInt(6) match
      case 0 => "\n  "
      case 1 => "  (* c *) "
      case 2 => "\n"
      case _ => " "
    val accepted = (0 until 300).count { _ =>
      val facts =
        (0 until 1 + rnd.nextInt(20)).map(_ => "r" + rnd.nextInt(3) + (0 until rnd.nextInt(4)).map(_ => space() + term(0)).mkString + ".")
      agrees("g.facts", facts.mkString("", "\n", "\n"))
    }
    // a term after a bare newline starts in column 0: those files are left to the parser
    assert(accepted > 30 && accepted < 300, s"$accepted accepted")
  }
