package hugin.fuzz

import hugin.syntax.{Parser, Printer}
import hugin.util.{Reporter, SourceFile}
import hugin.util.diagnostics.{Code, Phase}
import org.scalacheck.{Gen, Prop}

import scala.collection.concurrent.TrieMap

/** Resilience of the parser (issue #53, `docs/PARSER.md` §7): deleting or inserting one token of a valid
 *  corpus program, where that gives a syntax error,
 *
 *  - does not crash and finishes in time;
 *  - gives at most [[RecoveryFuzzSuite.k]] syntax errors;
 *  - gives no unresolved names (E0101) outside the damaged line: the names of an item with a syntax error
 *    are erroneous, and their uses are not reported. The exception is a declaration whose name the
 *    mutation destroyed (the name is then on the damaged line, and nothing can tell);
 *  - leaves the items from the first one in column 0 after the damaged line on parsed as before
 *    (recovery does not swallow the following items), unless the mutation opened a comment or a module
 *    body that is never closed (they extend to the end of the file by design).
 *
 *  A damaged `%infix` directive is excluded: its operator is unknown, which changes how the whole file
 *  is parsed. Errors of the object-level phases about items that use a dropped item (a rule that is not
 *  range-restricted without the `%demand` that was dropped) are not covered: an item dropped for any
 *  error has them, a syntax error is no different (`docs/NOTES.md`, "Parser (#53)"). */
class RecoveryFuzzSuite extends FuzzSuite:
  import RecoveryFuzzSuite.*

  override def shortCount: Int = 100

  property("one damaged token gives at most k syntax errors, no unresolved names, the items after it unchanged") {
    Prop.forAll(mutants) { m =>
      verdict("recovery", m.program, problems(m))
    }
  }

  private def problems(m: OneToken): List[String] =
    Fuzz.guarded(Fuzz.compile(m.program).reporter.diagnostics) match
      case Left(f) => List(s"compile: ${f.describe}")
      case Right(ds) if !ds.exists(_.code.phase == Phase.Syntax) => Nil // not a syntax error: not this property
      // a broken `%infix` changes how the whole file is parsed (its operator is unknown)
      case Right(_) if m.original.linesIterator.drop(m.line).nextOption().exists(_.contains("%infix")) => Nil
      case Right(ds) =>
        val errors = ds.filter(_.code.phase == Phase.Syntax)
        val tooMany = Option.when(errors.length > k)(s"${errors.length} syntax errors (at most $k expected):\n${show(errors)}")
        val cascading = ds.filter(d => d.code == Code.E0101 && !declarationLost(m, d) && d.primarySpan.startLine != m.mutantLine)
        val cascade = Option.when(cascading.nonEmpty)(s"unresolved names outside the damaged line:\n${show(cascading)}")
        val extending = ds.exists(d => d.code == Code.E0002 || (d.code == Code.E0005 && d.message.contains("`{`")))
        val swallowed = if extending then None else following(m)
        tooMany.toList ++ cascade ++ swallowed

  /** An unresolved name that the damaged line declared: when the mutation deletes the name of a
   *  declaration (or makes it unrecognisable), its uses cannot be resolved, and nothing can tell. */
  private def declarationLost(m: OneToken, d: hugin.util.Diagnostic): Boolean =
    val line = m.original.linesIterator.drop(m.line).nextOption().getOrElse("")
    // E0917: a name in quoted syntax that is not an object constant
    (d.code == Code.E0101 || d.code == Code.E0917) && line.split("[^A-Za-z0-9_']+").contains(d.primarySpan.text)

  private def show(ds: List[hugin.util.Diagnostic]): String =
    ds.map(d => s"  ${d.code.id} ${d.message} at ${d.primarySpan.show}").mkString("\n")

  /** The items of the original from the first one in column 0 after the line of the mutation on must be
   *  the last items of the mutant, unchanged. */
  private def following(m: OneToken): Option[String] =
    val original = items(m.original)
    val mutant = items(m.program.code)
    val first = original.indexWhere((line, col, _) => col == 0 && line > m.line)
    val after = if first < 0 then Nil else original.drop(first).map(_._3)
    val tail = mutant.map(_._3).takeRight(after.length)
    Option.when(tail != after)(s"the items after the damaged line changed:\n${after.mkString("\n")}\n---- became\n${tail.mkString("\n")}")

  /** The top-level items of a text: start line, start column and printed tree. */
  private def items(code: String): List[(Int, Int, String)] =
    Parser
      .parse(SourceFile.virtual("t.hgn", code), Reporter())
      .items
      .map(i => (i.span.startLine, i.span.startCol, Printer.showItem(i)))

object RecoveryFuzzSuite:
  /** The bound on the errors of one damaged token (decided in `docs/NOTES.md`, "Parser (#53)"). */
  val k = 2

  /** A corpus program with one token deleted or inserted; `line` is the (0-based) line of the mutation in
   *  the original, `mutantLine` in the mutant. */
  final case class OneToken(origin: String, original: String, program: Program, line: Int, mutantLine: Int):
    override def toString: String = s"mutant of $origin (line ${line + 1}):$program"

  /** The corpus programs that compile without errors (decided once per program, in-process). */
  private val validity = TrieMap.empty[String, Boolean]

  private def valid(e: Corpus.Entry): Boolean =
    validity.getOrElseUpdate(
      e.path,
      Fuzz.guarded(!Fuzz.compile(e.program).reporter.hasErrors).getOrElse(false)
    )

  private val candidates: Vector[Corpus.Entry] =
    Corpus.entries.filter(e => List("/run/", "/pos/", "examples/").exists(e.path.contains) && e.program.facts.isEmpty)

  private val specials = Vector("(", ")", "[", "]", "{", "}", ".", ",", ";", ":-", ":", "=", "|", "$", "\"", "->", "X", "p")

  val mutants: Gen[OneToken] =
    for
      e <- Gen.oneOf(candidates).suchThat(valid)
      pieces = Mutant.tokenize(e.program.code)
      n = pieces.length - 1 // the last piece is the end of the file
      if n > 0
      i <- Gen.choose(0, n - 1)
      insert <- Gen.oneOf(true, false)
      token <- Gen.frequency(1 -> Gen.oneOf(specials), 2 -> Gen.oneOf(pieces.init.map(_.text).filter(_.nonEmpty)))
    yield
      val mutated =
        if insert then pieces.patch(i, List(Piece(" ", token), pieces(i)), 1)
        else pieces.patch(i, Nil, 1)
      val code = mutated.map(_.code).mkString
      // the line of the inserted token, or of the deleted one; in the mutant, the line where it is or was
      val before = pieces.take(i).map(_.code).mkString.count(_ == '\n')
      val line = before + (if insert then 0 else pieces(i).gap.count(_ == '\n'))
      OneToken(e.path, e.program.code, e.program.copy(code = code), line, before)
