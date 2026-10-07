package hugin.util.diagnostics

import hugin.util.{Diagnostic, Origin, Span}

/** `--error-format=json`: one JSON object per diagnostic and line, modelled on rustc's format. The schema
 *  is versioned (`version`); fields are only added within a version.
 *
 *  {{{
 *  {"version":1,
 *   "code":{"id":"E0602","title":"...","explanation":"docs/errors/E0602.md"} | null,
 *   "level":"error"|"warning"|"note", "message":"...",
 *   "spans":[{"file","start":{"line","col"},"end":{"line","col"},"primary","label"}],
 *   "notes":["..."], "helps":["..."],
 *   "suggestions":[{"message","applicability","edits":[{"span":{...},"replacement"}]}],
 *   "origin":[{"description","span":{...}|null}],
 *   "rendered":"error[E0602]: ..."}
 *  }}}
 *
 *  Lines and columns are 1-based; columns count code points; `end` is exclusive. Spans without a source
 *  position are left out of `spans`. `rendered` is the terminal rendering without colour. */
object JsonDiagnostics:
  val Version = 1

  def encode(d: Diagnostic, rendered: String): Json =
    Json.obj(
      "version" -> Json.num(Version),
      "code" -> d.code.fold(Json.Null)(code),
      "level" -> Json.str(d.severity.label),
      "message" -> Json.str(d.message),
      "spans" -> Json.Arr(d.labels.filter(_.span.exists).map(l => span(l.span, Some(l.primary), Some(l.message)))),
      "notes" -> Json.Arr(d.notes.map(Json.str)),
      "helps" -> Json.Arr(d.helps.map(Json.str)),
      "suggestions" -> Json.Arr(d.suggestions.map(suggestion)),
      "origin" -> origin(d.origin),
      "rendered" -> Json.str(rendered)
    )

  private def code(c: Code): Json =
    Json.obj("id" -> Json.str(c.id), "title" -> Json.str(c.title), "explanation" -> Json.str(c.explanationPath))

  private def position(sp: Span, offset: Int): Json =
    val src = sp.source
    val line = src.lineOf(offset)
    Json.obj("line" -> Json.num(line + 1), "col" -> Json.num(src.columnOf(offset) + 1))

  private def span(sp: Span, primary: Option[Boolean], label: Option[String]): Json =
    val fields = List(
      "file" -> Json.str(sp.source.path),
      "start" -> position(sp, sp.start),
      "end" -> position(sp, sp.end)
    ) ++ primary.map("primary" -> Json.Bool(_)) ++ label.map("label" -> Json.str(_))
    Json.Obj(fields)

  private def suggestion(s: Suggestion): Json =
    Json.obj(
      "message" -> Json.str(s.message),
      "applicability" -> Json.str(s.applicability.toString),
      "edits" -> Json.Arr(s.edits.map(e => Json.obj("span" -> span(e.span, None, None), "replacement" -> Json.str(e.replacement))))
    )

  private def origin(o: Origin): Json =
    Json.Arr(o.frames.map(f =>
      Json.obj("description" -> Json.str(f.description), "span" -> (if f.span.exists then span(f.span, None, None) else Json.Null))
    ))
