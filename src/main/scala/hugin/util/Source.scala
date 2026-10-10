package hugin.util

/** A source file with lazily computed line table.
 *
 *  A file can also be a *slice*: the text of one top-level item of a file, parsed on its own so that its
 *  spans are item-relative (step 9 of `docs/INCREMENTALITY.md`). A slice is placed in its file at an
 *  offset ([[placedIn]], [[base]]), and spans into it resolve to positions in that file ([[Span.source]],
 *  [[Span.start]]): the placement is the boundary between item-relative and file positions. It is set
 *  when the file is split into items in a revision (`ItemSlices`), so results computed from a slice, and
 *  reused after an edit that moved the item, show the item's current positions. */
final class SourceFile(val path: String, val content: String):
  private var placement: SourceFile = this
  private var offset: Int = 0
  private var sliced: Boolean = false

  /** Whether this is a slice of a file (see above). */
  def isSlice: Boolean = sliced

  /** The file this source lies in: a slice's file as currently placed, otherwise the file itself. */
  def placedIn: SourceFile = placement

  /** The offset of this source in [[placedIn]] (0 for a file). */
  def base: Int = offset

  /** Places a slice at `offset` in `file` (the current revision's text of its file, which contains the
   *  slice's text there). */
  def place(file: SourceFile, offset: Int): Unit =
    require(sliced && !file.sliced && file.path == path, s"cannot place $path in ${file.path}")
    require(file.content.startsWith(content, offset), s"slice of $path does not lie at $offset")
    placement = file
    this.offset = offset

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
  def virtual(name: String, content: String): SourceFile = SourceFile(name, content)
  val NoSource: SourceFile = SourceFile("<no source>", "")

  /** A slice of the file `path` with the text `content`, placed nowhere yet (it lies in itself, so it is
   *  parsed in its own coordinates). */
  def slice(path: String, content: String): SourceFile =
    val s = SourceFile(path, content)
    s.sliced = true
    s

/** A half-open character range in a source file: `from` and `until` are offsets in `origin`, which is a
 *  file or a slice of one. `source`, `start` and `end` are the range in the file: for a slice, as it is
 *  currently placed. Equality and hashing use the origin (by identity) and its offsets, so they do not
 *  change when a slice is placed elsewhere. */
final case class Span(origin: SourceFile, from: Int, until: Int):
  def source: SourceFile = origin.placedIn
  def start: Int = origin.base + from
  def end: Int = origin.base + until
  def exists: Boolean = origin ne SourceFile.NoSource
  def to(other: Span): Span =
    if !exists then other
    else if !other.exists then this
    else if other.origin eq origin then Span(origin, from.min(other.from), until.max(other.until))
    else if other.source eq source then Span(source, start.min(other.start), end.max(other.end))
    else this

  /** The same range in `file`, the current text of this span's file, unless the span is in a slice (which
   *  is placed in the current text already). */
  def in(file: SourceFile): Span = if origin.isSlice then this else Span(file, start, end)

  /** An empty span at the start, or at the end, of this one (in the same origin). */
  def startPoint: Span = Span(origin, from, from)
  def endPoint: Span = Span(origin, until, until)
  def startLine: Int = source.lineOf(start)
  def startCol: Int = source.columnOf(start)
  def show: String = if exists then s"${source.path}:${startLine + 1}:${startCol + 1}" else "<synthetic>"
  def text: String = if exists then origin.content.substring(from, until.min(origin.content.length)) else ""
  override def toString: String = show

object Span:
  val NoSpan: Span = Span(SourceFile.NoSource, 0, 0)
