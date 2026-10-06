package hugin.repl

import hugin.util.*

/** A piece of the session text: an input as the user typed it, or a loaded program file.
 *
 *  `view` is the piece as a source file of its own (named `<input N>` or by the file's path); diagnostics
 *  are mapped to it. `text` is what the session contains: the same text, except that queries are blanked
 *  out once they have been answered, so offsets into `text` are offsets into `view`. */
final case class Chunk(view: SourceFile, text: String, file: Boolean):
  require(text.length == view.content.length)

  /** The chunk with the given ranges (relative to the chunk) replaced by spaces, keeping line breaks. */
  def blank(ranges: List[(Int, Int)]): Chunk =
    val chars = text.toCharArray
    for (start, end) <- ranges; i <- start until end if chars(i) != '\n' do chars(i) = ' '
    copy(text = String(chars))

object Chunk:
  def apply(view: SourceFile, file: Boolean): Chunk = Chunk(view, view.content, file)

/** The text of a session: its chunks joined by line breaks, kept as the input of the virtual file
 *  [[SessionText.path]]. Every chunk starts at a known offset, so a span into the session text maps back
 *  to the chunk it lies in (with the chunk's own lines and columns). */
final class SessionText(val chunks: Vector[Chunk]):
  /** The offset of each chunk in [[text]]. */
  val offsets: Vector[Int] = chunks.scanLeft(0)((offset, c) => offset + c.text.length + 1).take(chunks.length)

  val text: String = chunks.map(_.text).mkString("\n")

  /** The range of chunk `i` in [[text]]. */
  def range(i: Int): (Int, Int) = (offsets(i), offsets(i) + chunks(i).text.length)

  /** The chunk containing an offset of [[text]]; the line break after a chunk belongs to it. */
  private def chunkAt(offset: Int): Int = offsets.lastIndexWhere(_ <= offset)

  /** Maps a span into the session text to the chunk it starts in; other spans are unchanged. */
  def toChunk(span: Span): Span =
    if span.source.path != SessionText.path then span
    else
      chunkAt(span.start) match
        case -1 => span
        case i =>
          val (start, end) = range(i)
          val local = span.start.min(end) - start
          Span(chunks(i).view, local, (span.end.min(end) - start).max(local))

  /** Maps every span of a diagnostic, including the meta-level expansion chain. */
  def toChunks(d: Diagnostic): Diagnostic =
    d.copy(
      labels = d.labels.map(l => l.copy(span = toChunk(l.span))),
      origin = Origin(d.origin.frames.map(f => f.copy(span = toChunk(f.span))))
    )

object SessionText:
  /** The name of the virtual file holding the session text in the query database. */
  val path = "<repl>"
