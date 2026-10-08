package hugin.golden

/** Inline code annotations of negative golden tests, independent of wording (rustc's `//~ ERROR`): a
 *  comment `(*~ E0603 *)` on a line states that a diagnostic with that code is reported on that line,
 *  `(*~^ E0603 *)` on the line above (`^^` two lines above, and so on). A test that has annotations must
 *  account for exactly the diagnostics reported in its file, so a change of code or line fails even when
 *  the `.check` file is re-blessed. */
object Annotations:
  /** An expected or reported diagnostic: its code at a 1-based line. */
  final case class At(line: Int, code: String):
    override def toString: String = s"$code at line $line"

  private val annotation = """\(\*~(\^*)\s+([EW]\d{4})\s*\*\)""".r

  /** The annotations of a source text, sorted. */
  def expected(source: String): List[At] =
    source.linesIterator.zipWithIndex.flatMap { (text, i) =>
      annotation.findAllMatchIn(text).map(m => At(i + 1 - m.group(1).length, m.group(2)))
    }.toList.sortBy(a => (a.line, a.code))

  // matched against whole lines
  private val header = """(?:error|warning)\[([EW]\d{4})\].*""".r
  private val location = """\s*--> (.+):(\d+):\d+""".r

  /** The diagnostics of rendered output whose primary span lies in `file`, sorted: each header line
   *  `error[E…]` followed by its location line ` --> file:line:col`. */
  def reported(rendered: String, file: String): List[At] =
    rendered.linesIterator.sliding(2).flatMap {
      case Seq(header(code), location(path, line)) if path == file => Some(At(line.toInt, code))
      case _ => None
    }.toList.sortBy(a => (a.line, a.code))
