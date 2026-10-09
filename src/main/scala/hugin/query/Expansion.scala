package hugin.query

import hugin.obj.ObjPrinter
import hugin.util.{Origin, Span, TraceFrame}

/** The staged result of meta code, for language servers (issue #54): the object rules and queries that
 *  a directive application, a functor application or the item at a position became. Generated object
 *  items carry their expansion chain ([[hugin.util.Origin]]: `in expansion of %d …`, `in application of
 *  f`), whose frames lead back to the meta code that produced them.
 *
 *  The items are those of the object program as staging produced it (before the object-level phases
 *  transform it); a program with errors before staging has none. */
object Expansion:
  /** A staged item: its text, position and expansion chain. */
  final case class Item(text: String, span: Span, origin: Origin)

  /** What the meta code at a position expanded to: a title and the staged items. */
  final case class Result(title: String, items: List[Item]):
    /** As a Hugin text: a comment with the title, then each item, after a comment with the rest of its
     *  expansion chain (where it was produced inside the code shown). */
    def render(shown: TraceFrame => Boolean): String =
      val body = items.map { i =>
        val chain = i.origin.frames.filterNot(shown).map(f => s"(* ${f.description} at ${f.span.show} *)\n").mkString
        chain + i.text
      }
      (s"(* $title: ${count(items.length)} *)" :: body).mkString("\n") + "\n"

  private def count(n: Int) = if n == 1 then "1 item" else s"$n items"

  private def items(key: CompileKey)(using db: Database): List[Item] =
    val (rules, queries) = db(Compile, key).context.unit.staged
    rules.toList.map(r => Item(ObjPrinter.rule(r), r.span, r.origin)) ++
      queries.toList.map(q => Item(ObjPrinter.query(q), q.span, q.origin))

  private def covers(span: Span, path: String, offset: Int): Boolean =
    span.exists && span.source.path == path && span.start <= offset && offset <= span.end

  private def same(a: Span, b: Span): Boolean =
    a.exists && b.exists && a.source.path == b.source.path && a.start == b.start && a.end == b.end

  /** The code that produced generated items in a file: each frame (a directive or functor application)
   *  with the number of items it produced, in source order. */
  def sites(key: CompileKey, path: String)(using Database): List[(TraceFrame, Int)] =
    val all = items(key)
    all.flatMap(_.origin.frames).filter(f => f.span.exists && f.span.source.path == path).distinctBy(f => (f.span.start, f.span.end))
      .map(f => (f, all.count(_.origin.frames.exists(g => same(g.span, f.span)))))
      .sortBy(_._1.span.start)

  /** What the meta code at an offset expanded to: the innermost directive or functor application around
   *  it and the items it produced; otherwise the staged items of the item at the offset (the instances of
   *  a rule of a family or functor body). */
  def at(key: CompileKey, offset: Int)(using Database): Option[(Result, TraceFrame => Boolean)] =
    val all = items(key)
    val frames = all.flatMap(_.origin.frames).filter(f => covers(f.span, key.path, offset))
    frames.minByOption(f => f.span.end - f.span.start) match
      case Some(frame) =>
        val produced = all.filter(_.origin.frames.exists(g => same(g.span, frame.span)))
        val title = s"${frame.description.capitalize} at ${frame.span.show}"
        Some((Result(title, produced), (g: TraceFrame) => same(g.span, frame.span)))
      case None =>
        val here = all.filter(i => covers(i.span, key.path, offset))
        Option.when(here.nonEmpty) {
          val shown = here.map(_.span).minBy(sp => sp.end - sp.start)
          (Result(s"Staged code of the item at ${shown.show}", here.filter(i => same(i.span, shown))), (_: TraceFrame) => false)
        }

  /** [[at]], rendered as Hugin text. */
  def render(key: CompileKey, offset: Int)(using Database): Option[String] = at(key, offset).map((r, shown) => r.render(shown))
