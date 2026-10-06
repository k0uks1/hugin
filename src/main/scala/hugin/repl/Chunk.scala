package hugin.repl

/** A part of the session: an input as the user typed it (`path` is `<input N>`) or a loaded program file
 *  (`path` is the file's path, `file` is set). The part is a file of its own in the query database (the
 *  [[hugin.query.SourceText]] of `path`), so its diagnostics and `%import`s refer to it.
 *
 *  `text` is what `:list` shows: the text as compiled, with queries blanked out once they have been
 *  answered (offsets and line breaks are kept). */
final case class Chunk(path: String, text: String, file: Boolean):
  /** The chunk with the given ranges replaced by spaces, keeping line breaks. */
  def blank(ranges: List[(Int, Int)]): Chunk =
    val chars = text.toCharArray
    for (start, end) <- ranges; i <- start.max(0) until end.min(chars.length) if chars(i) != '\n' do chars(i) = ' '
    copy(text = String(chars))
