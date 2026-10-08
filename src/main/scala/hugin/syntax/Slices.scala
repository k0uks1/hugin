package hugin.syntax

import hugin.util.*
import scala.collection.mutable

/** Item slices (step 9 of `docs/INCREMENTALITY.md`): the top-level items of a file parsed from their own
 *  text, so that their spans are item-relative and an item whose text did not change is the same tree
 *  after an edit elsewhere in the file.
 *
 *  The file is parsed as a whole first: that parse decides where the items are (with its error recovery)
 *  and reports the parse diagnostics. The text of every item (from its first to its last character) is
 *  then parsed again on its own ([[Parser.parseSlice]], with the `%infix` operators of the whole file),
 *  placed at the item's offset ([[hugin.util.SourceFile.place]]) and used instead of the item from the
 *  whole file if it is [[congruent]] to it: the same tree with the same positions. An item that does not
 *  parse on its own without diagnostics, or differently, keeps the item from the whole file (with spans
 *  into it). */
object Slices:
  /** Identifies the slice of one item: its file, its text, the `%infix` operators of the file and how many
   *  items with the same text come before it in the file (identical items are different slices, since a
   *  slice has one placement). */
  final case class Key(path: String, text: String, infix: Map[String, (Parser.Assoc, Int)], occurrence: Int)

  /** A slice ([[hugin.util.SourceFile.slice]]) and its items, if it parses on its own without
   *  diagnostics. Compared by identity: a slice is placed in its file, so two slices with the same text
   *  are different slices. */
  final class Parsed(val source: SourceFile, val items: Option[List[Trees.Item]])

  def parse(key: Key): Parsed =
    val source = SourceFile.slice(key.path, key.text)
    Parsed(source, Parser.parseSlice(source, key.infix))

  /** The items of a parsed file, each from its slice where possible; `slice` parses a slice (memoised by
   *  the query database). Places the slices used for the file's current text. */
  def items(file: SourceFile, program: Program, slice: Key => Parsed): List[Trees.Item] =
    lazy val infix = Parser.infixOperators(file)
    val seen = mutable.HashMap.empty[String, Int]
    val all = program.items.toVector
    all.indices.toList.map { i =>
      val item = all(i)
      val sp = item.span
      // a directive attached to the declaration after it is parsed with it (it ends without a period)
      val attached = item match
        case Trees.Directive(_, Trees.DirArgs.Apply(_, Some(_))) => i + 1 < all.length
        case _ => false
      val end = if attached then all(i + 1).span.end else sp.end
      if !sp.exists || (sp.origin ne file) || end > file.content.length then item
      else
        val text = file.content.substring(sp.start, end)
        val occurrence = seen.getOrElse(text, 0)
        seen(text) = occurrence + 1
        val parsed = slice(Key(file.path, text, infix, occurrence))
        parsed.items match
          case Some(List(one)) if !attached =>
            parsed.source.place(file, sp.start)
            if congruent(item, one) then one else item
          case Some(List(one, _)) if attached =>
            parsed.source.place(file, sp.start)
            if congruent(item, one) then one else item
          case _ => item
    }

  /** Whether two trees are equal with the same positions: spans are compared by the file they lie in and
   *  their offsets there (a slice as placed), also the spans that trees keep in a second parameter list. */
  def congruent(a: Any, b: Any): Boolean = (a, b) match
    case (x: Span, y: Span) =>
      x.exists == y.exists && (!x.exists || ((x.source eq y.source) && x.start == y.start && x.end == y.end))
    case (x: Product, y: Product) =>
      x.getClass == y.getClass && x.productArity == y.productArity &&
      secondary(x).corresponds(secondary(y))(congruent) &&
      x.productIterator.corresponds(y.productIterator)(congruent)
    case (x: Iterable[?], y: Iterable[?]) => x.iterator.corresponds(y.iterator)(congruent)
    case _ => a == b

  /** The spans a tree keeps outside its fields. */
  private def secondary(x: Product): List[Span] = x match
    case s: Trees.Select => List(s.span, s.nameSpan)
    case i: Trees.Infix => List(i.span, i.opSpan)
    case i: Trees.Import => List(i.span, i.pathSpan)
    case d: Trees.Directive => List(d.span, d.kindSpan)
    case t: Tree => List(t.span)
    case i: Trees.Item => List(i.span)
    case _ => Nil
