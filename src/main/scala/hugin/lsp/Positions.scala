package hugin.lsp

import hugin.util.{SourceFile, Span}
import org.eclipse.lsp4j.{Position, Range}

/** Conversion between offsets into a [[hugin.util.SourceFile]] and LSP positions.
 *
 *  LSP positions are 0-based lines and columns counted in UTF-16 code units (the protocol's default
 *  position encoding). Offsets into a JVM string are UTF-16 indices as well, so an LSP column is the
 *  distance from the start of the line; [[hugin.util.SourceFile.columnOf]], which counts code points, differs from it
 *  after characters outside the Basic Multilingual Plane.
 */
object Positions:
  /** The LSP position of an offset (clamped to the file). */
  def position(source: SourceFile, offset: Int): Position =
    val off = offset.max(0).min(source.content.length)
    val line = source.lineOf(off)
    Position(line, off - source.lineStart(line))

  /** The offset of an LSP position. Lines past the end map to the end of the file, columns past the end of
   *  a line to the end of that line, and a column inside a surrogate pair to the start of the pair. */
  def offset(source: SourceFile, pos: Position): Int =
    if pos.getLine < 0 then 0
    else if pos.getLine >= source.lineCount then source.content.length
    else
      val start = source.lineStart(pos.getLine)
      val off = start + pos.getCharacter.max(0).min(source.lineText(pos.getLine).length)
      if off > start && off < source.content.length && Character.isLowSurrogate(source.content.charAt(off)) && Character.isHighSurrogate(
          source.content.charAt(off - 1)
        )
      then off - 1
      else off

  def range(span: Span): Range = Range(position(span.source, span.start), position(span.source, span.end))
