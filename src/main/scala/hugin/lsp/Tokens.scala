package hugin.lsp

import hugin.compiler.SemanticIndex
import hugin.util.SourceFile
import org.eclipse.lsp4j.SemanticTokens
import scala.collection.mutable
import scala.jdk.CollectionConverters.*

/** The semantic tokens of the language server: the classification of [[hugin.ide.Tokens]] (shared with
 *  `hugin highlight` and the browser build), encoded as the protocol requires. */
object Tokens:
  /** Token types and modifiers of the legend ([[hugin.ide.Tokens.types]], [[hugin.ide.Tokens.modifiers]]). */
  val types: List[String] = hugin.ide.Tokens.types
  val modifiers: List[String] = hugin.ide.Tokens.modifiers

  /** The tokens of a program file, encoded relative to the previous token as the protocol requires. */
  def of(ix: SemanticIndex, source: SourceFile, path: String): SemanticTokens =
    val data = mutable.ArrayBuffer.empty[Integer]
    var prevLine = 0
    var prevChar = 0
    for t <- hugin.ide.Tokens.tokens(ix, source, path) do
      val pos = Positions.position(t.span.source, t.span.start)
      val line = pos.getLine
      val char = pos.getCharacter
      // a token does not span lines (`'(` and `$..` never do)
      val length = (t.span.end - t.span.start).min(t.span.source.lineText(line).length - char)
      data ++= List(line - prevLine, if line == prevLine then char - prevChar else char, length, t.tpe, t.mods).map(Int.box)
      prevLine = line
      prevChar = char
    SemanticTokens(data.asJava)
