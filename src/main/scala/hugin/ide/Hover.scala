package hugin.ide

import hugin.query.{CompileKey, Database, Ide, MetaIde}

/** What hover shows at a position: the signature of the name there (a symbol's description as seen at
 *  this use, or the type of an object variable), and notes on what the compiler decided there (staging,
 *  family instances) and on the meta level (the goal of a hole, a directive's application, the type and
 *  stage of the expression). Notes may contain code in backticks, and the meta level's notes Markdown
 *  emphasis and code blocks. */
final case class Hover(signature: Option[String], notes: List[String]):
  /** The hover as plain lines (`hugin query hover`): the signature, then the notes, without the
   *  Markdown line breaks (two spaces at the end of a line) of the meta level's notes. */
  def text: String = (signature.toList ++ notes).mkString("\n").replace("  \n", "\n")

object Hover:
  /** The hover at an offset of the program `key`: [[hugin.query.Ide.hoverInfo]] and, on a token (not
   *  between tokens), [[hugin.query.MetaIde.hover]], without the notes both give. Nothing in a facts
   *  file, or where neither knows anything. */
  def at(key: CompileKey, offset: Int)(using Database): Option[Hover] =
    if Files.isFacts(key.path) then None
    else
      val info = Ide.hoverInfo(key, offset)
      val notes = info.toList.flatMap(_.notes)
      val text = Files.source(key.path).content
      def onToken(i: Int) = i >= 0 && i < text.length && !text.charAt(i).isWhitespace
      val meta = if onToken(offset) || onToken(offset - 1) then MetaIde.hover(key, offset) else Nil
      val signature = info.flatMap(_.signature)
      val all = notes ++ meta.filterNot(notes.contains)
      Option.when(signature.isDefined || all.nonEmpty)(Hover(signature, all))
