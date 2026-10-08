package hugin.compiler

import hugin.util.Span
import hugin.util.diagnostics.*
import scala.language.implicitConversions

/** The problems of resolving imports (E0108). Paths are as written in the import, files as resolved. */
enum ImportError extends Problem:
  /** Files import each other: `cycle` lists the files from the importing file back to itself. */
  case Cycle(path: String, at: Span, cycle: List[String])
  case Missing(path: String, at: Span, resolved: String)
  case PreludeMissing

  def code: Code = Code.E0108

  def primary: Span = this match
    case Cycle(_, s, _) => s
    case Missing(_, s, _) => s
    case PreludeMissing => Span.NoSpan

  def message: Msg = this match
    case Cycle(p, _, _) => msg"cyclic import of ${Src(p)}"
    case Missing(p, _, _) => msg"cannot find ${Src(p)}"
    case PreludeMissing => msg"the prelude is missing from this installation"

  override def primaryLabel: Msg = this match
    case _: Cycle => msg"imported here"
    case _: Missing => msg"no such file"
    case PreludeMissing => Msg.empty

  override def notes: List[Msg] = this match
    case Cycle(_, _, c) => List(msg"import cycle: ${Lit(c.mkString(" -> "))}")
    case Missing(_, _, r) => List(msg"resolved to ${Src(r)}")
    case PreludeMissing => Nil

  override def helps: List[Msg] = this match
    case _: Cycle => List(msg"a file is a module body; move what both files need into a third file")
    case _ => Nil
