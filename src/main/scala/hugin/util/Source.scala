package hugin.util

import java.nio.file.{Files, Path}

/** A source file with lazily computed line table. */
final class SourceFile(val path: String, val content: String):
  private lazy val lineStarts: Array[Int] =
    val b = Array.newBuilder[Int]
    b += 0
    var i = 0
    while i < content.length do
      if content.charAt(i) == '\n' then b += i + 1
      i += 1
    b.result()

  /** 0-based line of an offset. */
  def lineOf(offset: Int): Int =
    val off = offset.max(0).min(content.length)
    var lo = 0
    var hi = lineStarts.length - 1
    while lo < hi do
      val mid = (lo + hi + 1) / 2
      if lineStarts(mid) <= off then lo = mid else hi = mid - 1
    lo

  def lineStart(line: Int): Int = lineStarts(line)

  def lineCount: Int = lineStarts.length

  /** Text of a 0-based line without the trailing newline. */
  def lineText(line: Int): String =
    val s = lineStarts(line)
    val e = if line + 1 < lineStarts.length then lineStarts(line + 1) - 1 else content.length
    content.substring(s, e.max(s)).stripSuffix("\r")

  /** 0-based column measured in code points. */
  def columnOf(offset: Int): Int =
    val off = offset.max(0).min(content.length)
    val s = lineStarts(lineOf(off))
    content.codePointCount(s, off)

  /** The offset of a 0-based line and code-point column, if inside the file. */
  def offset(line: Int, column: Int): Option[Int] =
    if line < 0 || line >= lineCount then None
    else
      val start = lineStarts(line)
      val text = lineText(line)
      if column < 0 || column > text.codePointCount(0, text.length) then None
      else Some(start + text.offsetByCodePoints(0, column))

  override def toString: String = path

object SourceFile:
  def fromPath(p: Path): SourceFile = SourceFile(p.toString, Files.readString(p))
  def virtual(name: String, content: String): SourceFile = SourceFile(name, content)
  val NoSource: SourceFile = SourceFile("<no source>", "")

/** A half-open character range in a source file. */
final case class Span(source: SourceFile, start: Int, end: Int):
  def exists: Boolean = source ne SourceFile.NoSource
  def to(other: Span): Span =
    if !exists then other
    else if !other.exists || (other.source ne source) then this
    else Span(source, start.min(other.start), end.max(other.end))
  def startLine: Int = source.lineOf(start)
  def startCol: Int = source.columnOf(start)
  def show: String = if exists then s"${source.path}:${startLine + 1}:${startCol + 1}" else "<synthetic>"
  def text: String = if exists then source.content.substring(start, end.min(source.content.length)) else ""
  override def toString: String = show

object Span:
  val NoSpan: Span = Span(SourceFile.NoSource, 0, 0)
