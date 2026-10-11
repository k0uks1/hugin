package hugin.web

import hugin.compiler.Compiler
import hugin.ide.{Annotations, Highlighting}
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
    if evaluate && !denied && request.settings.stopAfter.isEmpty then
      Platform.deadline = request.budgetMs.fold(Double.PositiveInfinity)(start + _)
      try
        val outcome = db(Evaluate, EvaluateKey(key, Nil, request.allRelations))
        diagnostics = diagnostics ++ outcome.diagnostics
        evaluation = outcome.result
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
