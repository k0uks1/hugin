package hugin.web

import hugin.compiler.Compiler
import hugin.ide.{Annotations, Completion, Expansions, FixKind, Fixes, Highlighting}
import hugin.platform.Platform
import hugin.query.*
import hugin.runtime.Evaluation
import hugin.util.{Diagnostic, DiagnosticRenderer}
import hugin.util.diagnostics.{Json, JsonDiagnostics, LintLevels}
import scala.scalajs.js
import scala.util.control.NonFatal

/** What `hugin check` and `hugin run` do, on one program held in memory, with the results as JSON (see
 *  [[Hugin]] for the format), and the editor's analysis of the program (`analyse`: the highlighting and the
 *  annotation table, `docs/design/web-ide.md`). Every call works in the persistent database of [[Session]],
 *  so a call on the text of the previous one reuses its compilation. */
object Playground:
  val Version = 1

  def compile(source: String, options: js.UndefOr[js.Any], evaluate: Boolean): String =
    Request.read(options) match
      case Left(problem) => failure(problem)
      case Right(request) =>
        guarded(result(source, request, evaluate).render)

  /** The highlighting of the program alone (no diagnostics, no evaluation), for the editor while the
   *  reader types: `{ "version": 1, "tokens": [[text, [class, …]], …] }`. */
  def highlight(source: String, options: js.UndefOr[js.Any]): String =
    Request.read(options) match
      case Left(problem) => failure(problem)
      case Right(request) =>
        guarded {
          given db: Database = Session.db
          db.set(SourceText, request.file, source)
          Json.obj(
            "version" -> Json.num(Version),
            "tokens" -> tokens(request, db(Compile, CompileKey(request.file, request.settings)).index)
          ).render
        }

  /** The editor's analysis of the program after a pause in typing (no diagnostics, no evaluation): the
   *  highlighting and the annotation table, `{ "version": 1, "tokens": …, "info": … }` ([[Session.info]]). */
  def analyse(source: String, options: js.UndefOr[js.Any]): String =
    Request.read(options) match
      case Left(problem) => failure(problem)
      case Right(request) =>
        guarded {
          given db: Database = Session.db
          db.set(SourceText, request.file, source)
          val key = CompileKey(request.file, request.settings)
          Json.obj("version" -> Json.num(Version), "tokens" -> tokens(request, db(Compile, key).index), "info" -> info(request, key)).render
        }

  /** The completions at an offset of the program (UTF-16 code units), from `hugin.ide.Completion`:
   *  `{ "version": 1, "from": n, "items": [{ "label", "kind", "detail", "fits" }, …], "ranked": bool }`.
   *  The items replace the text from `from` to the offset; `kind` is `hugin.ide.CandidateKind`'s name
   *  with a lowercase initial (`relation`, `metaDefinition`, …); if `ranked`, the type expected there is
   *  known and `fits` marks the candidates whose result type fits it. */
  def complete(source: String, offset: Int, options: js.UndefOr[js.Any]): String =
    Request.read(options) match
      case Left(problem) => failure(problem)
      case Right(request) =>
        guarded {
          given db: Database = Session.db
          db.set(SourceText, request.file, source)
          val cs = Completion.at(CompileKey(request.file, request.settings), offset.max(0).min(source.length))
          val items = cs.items.map { c =>
            Json.obj(
              "label" -> Json.str(c.label),
              "kind" -> Json.str(c.kind.toString.head.toLower.toString + c.kind.toString.tail),
              "detail" -> Json.str(c.detail),
              "fits" -> Json.Bool(c.fits)
            )
          }
          Json.obj(
            "version" -> Json.num(Version),
            "from" -> Json.num(cs.from.toLong),
            "items" -> Json.Arr(items),
            "ranked" -> Json.Bool(cs.ranked)
          ).render
        }

  /** The fixes and the actions of interactive development for the part `[from, to]` of the program
   *  (UTF-16 code units), from `hugin.ide.Fixes`: `{ "version": 1, "actions": [{ "title", "kind",
   *  "preferred", "edits": [{ "from", "to", "insert" }] }, …] }`. `kind` is `quickfix` or `rewrite`; only
   *  actions whose edits all lie in the program are listed. */
  def actions(source: String, from: Int, to: Int, options: js.UndefOr[js.Any]): String =
    Request.read(options) match
      case Left(problem) => failure(problem)
      case Right(request) =>
        guarded {
          given db: Database = Session.db
          db.set(SourceText, request.file, source)
          val (a, b) = (from.max(0).min(source.length), to.max(0).min(source.length))
          val fixes = Fixes.at(CompileKey(request.file, request.settings), request.file, a.min(b), a.max(b))
          val actions =
            fixes.filter(f => f.edits.nonEmpty && f.edits.forall(e => e.span.exists && e.span.source.path == request.file)).map {
              f =>
                Json.obj(
                  "title" -> Json.str(f.title),
                  "kind" -> Json.str(if f.kind == FixKind.QuickFix then "quickfix" else "rewrite"),
                  "preferred" -> Json.Bool(f.preferred),
                  "edits" -> Json.Arr(f.edits.map(e =>
                    Json.obj("from" -> Json.num(e.span.start.toLong), "to" -> Json.num(e.span.end.toLong), "insert" -> Json.str(e.text))
                  ))
                )
            }
          Json.obj("version" -> Json.num(Version), "actions" -> Json.Arr(actions)).render
        }

  /** What the meta code at an offset (UTF-16 code units) of the program expanded to, from
   *  `hugin.ide.Expansions`: the object rules and queries of the innermost directive or functor
   *  application around it (or of the item there), as Hugin text: `{ "version": 1, "text": "…" }`, with
   *  `text` null if there is none. */
  def expansion(source: String, offset: Int, options: js.UndefOr[js.Any]): String =
    Request.read(options) match
      case Left(problem) => failure(problem)
      case Right(request) =>
        guarded {
          given db: Database = Session.db
          db.set(SourceText, request.file, source)
          val text = Expansions.at(CompileKey(request.file, request.settings), offset.max(0).min(source.length))
          Json.obj("version" -> Json.num(Version), "text" -> text.fold(Json.Null)(Json.str)).render
        }

  /** The annotation table of the program, as [[Session.info]] encodes it. */
  private def info(request: Request, key: CompileKey)(using Database): Json =
    Session.info(Annotations.of(key, request.file), request.file)

  /** The JSON of `body`, or an internal error, after which the session starts a new database. */
  private def guarded(body: => String): String =
    try body
    catch
      case NonFatal(e) =>
        Session.reset()
        failure(s"internal error: $e")
      case e: StackOverflowError =>
        Session.reset()
        failure(s"internal error: $e")

  /** The runs of the program's text and their classes, as `hugin highlight` computes them. */
  private def tokens(request: Request, index: => hugin.compiler.SemanticIndex)(using db: Database): Json =
    val runs = Highlighting.runs(db(Parse, request.file).source, request.file, index)
    Json.Arr(runs.map(r => Json.Arr(List(Json.str(r.text), Json.Arr(r.classes.map(Json.str))))))

  /** The phases, as `hugin phases` lists them: `[{"name": …, "description": …}]`. */
  def phases: String =
    Json.Arr(Compiler.phasePlan.flatten.map(p => Json.obj("name" -> Json.str(p.phaseName), "description" -> Json.str(p.description)))).render

  private def failure(message: String): String = Json.obj("version" -> Json.num(Version), "error" -> Json.str(message)).render

  private def result(source: String, request: Request, evaluate: Boolean): Json =
    val start = js.Date.now()
    given db: Database = Session.db
    db.set(SourceText, request.file, source)
    val key = CompileKey(request.file, request.settings)
    val compiled = db(Compile, key)
    val denied = LintLevels.hasErrors(request.display.shown(compiled.diagnostics))
    var diagnostics = compiled.diagnostics
    var evaluation: Option[Evaluation.Result] = None
    var cancelled = false
    var summary: Option[String] = None
    if evaluate && !denied && request.settings.stopAfter.isEmpty then
      Platform.deadline = request.budgetMs.fold(Double.PositiveInfinity)(start + _)
      try
        val outcome = db(Evaluate, EvaluateKey(key, Nil, request.allRelations))
        diagnostics = diagnostics ++ outcome.diagnostics
        evaluation = outcome.result
        // `--certify`: the verdict of std/certify on the run
        if request.settings.certify && evaluation.isDefined then
          val certified =
            hugin.runtime.Certify(compiled.context.unit, compiled.context.unit.core.nn, db(Fixpoint, FixpointKey(key, Nil)).get.engine)
          diagnostics = diagnostics ++ certified.diagnostics
          summary = certified.summary
      catch case _: InterruptedException => cancelled = true
      finally Platform.deadline = Double.PositiveInfinity
    val shown = request.display.shown(diagnostics)
    val ran = !evaluate || request.settings.stopAfter.isDefined || evaluation.isDefined
    val strings = (xs: List[String]) => Json.Arr(xs.map(Json.str))
    Json.obj(
      "version" -> Json.num(Version),
      "ok" -> Json.Bool(!LintLevels.hasErrors(shown) && !cancelled && ran),
      "diagnostics" -> Json.Arr(shown.map(encode)),
      "printed" -> (if compiled.printed.isEmpty then Json.Null else Json.str(compiled.printed.mkString("\n"))),
      "evaluated" -> Json.Bool(evaluation.isDefined),
      "certified" -> summary.fold(Json.Null)(Json.str),
      "cancelled" -> Json.Bool(cancelled),
      "facts" -> strings(evaluation.fold(Nil)(_.facts)),
      "answers" -> Json.Arr(evaluation.fold(Nil)(_.answers).map { a =>
        Json.obj(
          "query" -> Json.str(a.query),
          "vars" -> strings(a.vars),
          "rows" -> Json.Arr(a.rows.map(strings)),
          "lines" -> strings(a.lines)
        )
      }),
      "relations" -> Json.Arr(evaluation.fold(Nil)(_.relations).map { r =>
        Json.obj("name" -> Json.str(r.name), "vars" -> strings(Nil), "rows" -> Json.Arr(r.rows.map(strings)))
      }),
      "output" -> strings(compiled.printed ++ evaluation.fold(Nil)(_.output)),
      "tokens" -> tokens(request, compiled.index),
      "info" -> info(request, key),
      "timeMs" -> Json.num((js.Date.now() - start).round)
    )

  private val plain = DiagnosticRenderer(color = false)

  private def encode(d: Diagnostic): Json = JsonDiagnostics.encode(d, plain.render(d))
