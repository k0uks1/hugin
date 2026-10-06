package hugin.repl

import hugin.syntax.{Lexer, Tok}
import hugin.util.{Reporter, SourceFile}

/** Classifies what the user has typed so far, using the lexer (so periods inside comments, strings and
 *  selectors `a.b` are not mistaken for the end of an item). */
object Input:
  enum Status:
    /** Only whitespace and comments. */
    case Empty

    /** A command `:name args`; commands are one line. */
    case Command

    /** One or more items, the last terminated by its period at nesting depth 0. */
    case Complete

    /** The last item is still open: no final period yet, an open bracket, or an unterminated comment. */
    case Incomplete

  /** Whether the input is a command: its first non-blank characters are `:` and a letter. */
  def isCommand(text: String): Boolean =
    val t = text.stripLeading
    t.length >= 2 && t.charAt(0) == ':' && t.charAt(1).isLetter

  def status(text: String): Status =
    if isCommand(text) then return Status.Command
    val lexer = Lexer(SourceFile.virtual("<input>", text), Reporter())
    val tokens = lexer.tokenize().filter(_.kind != Tok.EOF)
    if lexer.unterminatedComment then Status.Incomplete
    else if tokens.isEmpty then Status.Empty
    // other lexical errors cannot be repaired by reading on (strings end at the line); report them
    else if tokens.exists(_.kind == Tok.Error) then Status.Complete
    else
      val depths = tokens.scanLeft(0) { (depth, t) =>
        t.kind match
          case Tok.LParen | Tok.LBrack | Tok.LBrace => depth + 1
          case Tok.RParen | Tok.RBrack | Tok.RBrace => depth - 1
          case _ => depth
      }
      // an unmatched closing bracket is an error that more input cannot fix
      if depths.exists(_ < 0) then Status.Complete
      else if depths.last == 0 && tokens.last.kind == Tok.Period then Status.Complete
      else Status.Incomplete

  /** Whether the input can be executed, or more lines are needed. */
  def isComplete(text: String): Boolean = status(text) != Status.Incomplete
