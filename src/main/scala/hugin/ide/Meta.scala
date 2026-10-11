package hugin.ide

import hugin.compiler.MetaIndex.{Goal, Hint, HintKind}
import hugin.query.{CompileKey, Database, Expansion, MetaIde}
import hugin.util.{Diagnostic, Span}
import hugin.util.diagnostics.Code

/** Which inlay hints to show: the conversions stage inference inserted (`staging`), inferred implicit
 *  arguments (`implicits`) and universe levels (`levels`). */
final case class HintSettings(staging: Boolean = true, implicits: Boolean = true, levels: Boolean = false):
  def kinds: Set[HintKind] =
    Set(HintKind.Staging -> staging, HintKind.Implicit -> implicits, HintKind.Level -> levels).collect { case (k, true) => k }

/** Inlay hints. */
object Hints:
  /** The inlay hints of the kinds `settings` selects in the part `[from, to]` of the file `path` of the
   *  program `key`, in order. */
  def in(key: CompileKey, path: String, from: Int, to: Int, settings: HintSettings)(using Database): List[Hint] =
    if Files.isFacts(path) then Nil else MetaIde.hints(key, path, from, to, settings.kinds)

/** The goals of typed holes. */
object Goals:
  /** The goal of the typed hole at `span` (in any file of the program `key`). */
  def at(key: CompileKey, span: Span)(using Database): Option[Goal] =
    if span.exists then MetaIde.goalAt(key, span.start, Some(span.source.path)) else None

  /** The goal of the hole a diagnostic reports (E0924), from the compilation `key`. */
  def of(key: CompileKey, d: Diagnostic)(using Database): Option[Goal] =
    if d.code == Code.E0924 then at(key, d.primarySpan) else None

/** The staged result of meta code ([[hugin.query.Expansion]]). */
object Expansions:
  /** What the meta code at an offset of the program `key` expanded to, as Hugin text. */
  def at(key: CompileKey, offset: Int)(using Database): Option[String] =
    if Files.isFacts(key.path) then None else Expansion.render(key, offset)

  /** The directive and functor applications in the file `path` that produced object items, each with
   *  the number of items it produced, in source order. */
  def sites(key: CompileKey, path: String)(using Database): List[(Span, Int)] =
    if Files.isFacts(path) then Nil else Expansion.sites(key, path).map((frame, n) => (frame.span, n))
