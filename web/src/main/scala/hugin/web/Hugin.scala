package hugin.web

import scala.scalajs.js
import scala.scalajs.js.annotation.{JSExport, JSExportTopLevel}

/** The browser API of the compiler: the global `Hugin` of `hugin.js` (a classic script) and the export
 *  `Hugin` of `hugin.mjs` (an ES module). Each function returns a JSON text:
 *
 *  {{{
 *  { "version": 1,
 *    "ok": true,              // no error shown, not cancelled, and (for run) the program was evaluated
 *    "diagnostics": [ … ],    // the JSON diagnostics of `--error-format=json` (version 1), lint levels applied
 *    "printed": "…",          // the text of `printAfter` (and `explainTermination`), or null
 *    "evaluated": true, "cancelled": false,
 *    "facts": [ "path a b.", … ],
 *    "answers": [ { "query": "?- path a X.", "vars": ["X"], "rows": [["b"], ["c"]], "lines": ["X = b.", "X = c."] } ],
 *    "relations": [ { "name": "path", "vars": [], "rows": [["a", "b"], …] } ],   // the shown relations
 *    "output": [ … ],         // what `hugin run` prints on stdout: printed, facts, then queries and answers
 *    "tokens": [ ["text", ["class", …]], … ],   // the highlighting, as `hugin highlight` (runs covering the program)
 *    "info": { "names": …, "hovers": …, "hints": … },   // the annotation table (Session.info)
 *    "timeMs": 42 }
 *  }}}
 *
 *  or `{ "version": 1, "error": "…" }` for an invalid option or an internal error. The program may import
 *  the `std/` modules; any other import is reported as missing (E0108). The options are those of
 *  [[Request.read]], as an object or its JSON text. All calls share one query database ([[Session]]): a
 *  call on the same text as the previous one reuses its compilation. */
@JSExportTopLevel("Hugin")
object Hugin:
  /** The version of the result format. */
  @JSExport val version: Int = Playground.Version

  /** Compiles the program, as `hugin check`. */
  @JSExport def check(source: String, options: js.UndefOr[js.Any] = js.undefined): String =
    Playground.compile(source, options, evaluate = false)

  /** Compiles and evaluates the program, as `hugin run`. */
  @JSExport def run(source: String, options: js.UndefOr[js.Any] = js.undefined): String =
    Playground.compile(source, options, evaluate = true)

  /** The highlighting of the program only (no diagnostics, no evaluation): `{ "version": 1, "tokens": … }`. */
  @JSExport def highlight(source: String, options: js.UndefOr[js.Any] = js.undefined): String =
    Playground.highlight(source, options)

  /** The editor's analysis of the program (no diagnostics, no evaluation): `{ "version": 1, "tokens": …,
   *  "info": … }`, the highlighting and the annotation table from which the playground answers hover,
   *  go to definition, occurrences and references (`docs/design/web-ide.md`, 5.2). */
  @JSExport def analyse(source: String, options: js.UndefOr[js.Any] = js.undefined): String =
    Playground.analyse(source, options)

  /** The completions at an offset (UTF-16 code units) of the program: `{ "version": 1, "from": …, "items":
   *  [{ "label", "kind", "detail", "fits" }, …], "ranked": … }` (`docs/design/web-ide.md`, 5.2). */
  @JSExport def complete(source: String, offset: Int, options: js.UndefOr[js.Any] = js.undefined): String =
    Playground.complete(source, offset, options)

  /** The fixes and the actions of interactive development (split, add the missing clauses, add a clause,
   *  refine a hole, and the diagnostics' suggestions) for the part `[from, to]` (UTF-16 code units) of the
   *  program: `{ "version": 1, "actions": [{ "title", "kind", "preferred", "edits": [{ "from", "to",
   *  "insert" }] }, …] }` (`docs/design/web-ide.md`, 5.2). */
  @JSExport def actions(source: String, from: Int, to: Int, options: js.UndefOr[js.Any] = js.undefined): String =
    Playground.actions(source, from, to, options)

  /** What the meta code at an offset (UTF-16 code units) expanded to: the object rules and queries of the
   *  directive or functor application around it, as Hugin text: `{ "version": 1, "text": … }` (null if
   *  none; `docs/design/web-ide.md`, 5.2). */
  @JSExport def expansion(source: String, offset: Int, options: js.UndefOr[js.Any] = js.undefined): String =
    Playground.expansion(source, offset, options)

  /** Makes the current Web Worker answer messages ([[WorkerMain]]); for a worker without a handler of
   *  its own: `importScripts("hugin.js"); Hugin.serveWorker()`. */
  @JSExport def serveWorker(): Unit = WorkerMain.serve()

  /** The compiler's phases in order, for `printAfter`: `[{ "name": …, "description": … }]`. */
  @JSExport def phases(): String = Playground.phases
