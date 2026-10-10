package hugin.query

import hugin.compiler.{MetaIndex, SemanticIndex}
import hugin.compiler.MetaIndex.*
import hugin.util.Span

/** Position queries on the meta level for language servers (issue #54), from the [[MetaIndex]] the
 *  elaborator fills: the elaborated type and stage of the expression at a position, goals of typed holes,
 *  directive applications, the stages of shared types, inlay hints and what interactive development
 *  needs (case splits, missing clauses, clause skeletons, the expected type for completion).
 *
 *  Kept apart from [[Ide]], whose answers (`hugin query`, the REPL's `:type`) stay as they are. */
object MetaIde:
  private def index(key: CompileKey)(using db: Database): SemanticIndex = db(Compile, key).index
  private def meta(key: CompileKey)(using Database): MetaIndex = index(key).meta

  private def covers(span: Span, path: String, offset: Int): Boolean =
    span.exists && span.source.path == path && span.start <= offset && offset <= span.end

  private def size(span: Span): Int = span.end - span.start

  /** The innermost expression around an offset with its elaborated type and stage. */
  def typedAt(key: CompileKey, offset: Int, in: Option[String] = None)(using Database): Option[Typed] =
    val path = in.getOrElse(key.path)
    meta(key).typesWhere(covers(_, path, offset)).minByOption(t => size(t.span))

  /** The goal of the typed hole at an offset. */
  def goalAt(key: CompileKey, offset: Int, in: Option[String] = None)(using Database): Option[Goal] =
    val path = in.getOrElse(key.path)
    meta(key).goals.find(g => covers(g.span, path, offset))

  /** The goals of the holes in a file. */
  def goals(key: CompileKey, path: String)(using Database): List[Goal] =
    meta(key).goals.filter(g => g.span.exists && g.span.source.path == path).toList

  /** The directive application around an offset. */
  def directiveAt(key: CompileKey, offset: Int, in: Option[String] = None)(using Database): Option[DirectiveUse] =
    val path = in.getOrElse(key.path)
    meta(key).directives.filter(d => covers(d.span, path, offset)).minByOption(d => size(d.span))

  /** What hover adds for the meta level, as Markdown paragraphs: the goal of a hole, a directive's
   *  application, the stages of a shared type, and the type and stage of the expression. */
  def hover(key: CompileKey, offset: Int, in: Option[String] = None)(using Database): List[String] =
    val goal = goalAt(key, offset, in).toList.flatMap(goalText)
    val directive = directiveAt(key, offset, in).toList.map { d =>
      s"directive application `${short(d.shown)}` : `${d.tpe}`  \nfootprint: ${d.footprint}"
    }
    val shared = Ide.symbolAt(key, offset, in).toList.flatMap(meta(key).notes)
    // a directive's arguments are quoted as data: the application says what they are
    val typed = if goal.nonEmpty || directive.nonEmpty then Nil else typedAt(key, offset, in).toList.flatMap(typedText)
    goal ++ directive ++ shared ++ typed

  /** A goal as hover text: its type and stage, then the variables in scope. */
  def goalText(g: Goal): List[String] =
    val name = "?" + g.name.getOrElse("")
    val context = if g.context.isEmpty then "" else g.context.map((x, t) => s"$x : $t").mkString("\n\n```hugin\n", "\n", "\n```")
    List(s"**goal** `$name` : `${g.tpe}` (${g.stage} level)$context")

  private def typedText(t: Typed): List[String] =
    val stage = if t.code then s"meta, object code `${t.tpe}`" else t.stage
    val main = s"`${short(t.span.text)}` : `${t.tpe}`  \nstage: $stage"
    main :: t.elaborated.map(e => s"elaborated: `$e`").toList

  /** A text on one line, at most a few dozen characters. */
  private def short(s: String): String =
    val line = s.replaceAll("\\s+", " ").trim
    if line.length > MaxText then line.take(MaxText - 1) + "…" else line

  private val MaxText = 60

  /** The inlay hints in the part `[from, to]` of a file, of the given kinds. */
  def hints(key: CompileKey, path: String, from: Int, to: Int, kinds: Set[HintKind])(using Database): List[Hint] =
    meta(key).hints
      .filter(h => kinds(h.kind) && h.at.exists && h.at.source.path == path && from <= h.at.start && h.at.start <= to)
      .toList
      .sortBy(h => (h.at.start, h.kind.ordinal))

  /** The pattern variable at an offset that can be split. */
  def splitAt(key: CompileKey, offset: Int)(using Database): Option[Split] =
    meta(key).splits.find(s => covers(s.variable, key.path, offset))

  /** The clauses missing from the function whose E0911 is reported at `at`. */
  def missingAt(key: CompileKey, at: Span)(using Database): Option[MissingClauses] =
    meta(key).missingClauses.find(m => m.at.exists && m.at.source.path == at.source.path && m.at.start == at.start)

  /** The skeleton of the clauses of a function declared (without clauses) around an offset. */
  def skeletonAt(key: CompileKey, offset: Int)(using Database): Option[Skeleton] =
    meta(key).skeletons.find(s => covers(s.decl, key.path, offset))

  /** The head of the type expected at the expression from `start` to `end` of `path` (an identifier being
   *  typed), if the elaborator checked it against a known type, with the variables in scope there (known
   *  if its elaboration failed). */
  def expectedAt(key: CompileKey, path: String, start: Int, end: Int)(using Database): Option[(String, List[(String, String)])] =
    meta(key)
      .typesWhere(sp => sp.exists && sp.source.path == path && sp.start == start && sp.end == end)
      .find(t => t.checked && t.head.nonEmpty)
      .map(t => (t.head, t.context))

  /** The heads of the result types of the symbols named `name` in the index (completion candidates). A
   *  name that the program's files declare stands for their symbols only: a declaration of the standard
   *  library with the same name (`size` of `std/list`) is not in scope there, or is shadowed. */
  def headsByName(key: CompileKey)(using Database): Map[String, Set[String]] =
    val ix = index(key)
    (ix.symbols ++ ix.topLevel).groupBy(_.name).view.mapValues { syms =>
      val own = syms.filterNot(s => hugin.compiler.StdlibCache.isStdlib(s.span.source.path))
      (if own.nonEmpty then own else syms).flatMap(ix.meta.resultHeadOf).toSet
    }.toMap

  /** The head of the result type of a symbol (completion candidates). */
  def resultHead(key: CompileKey, sym: hugin.compiler.Sym)(using Database): Option[String] = meta(key).resultHeadOf(sym)
