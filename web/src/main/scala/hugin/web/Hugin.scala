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
 *    "timeMs": 42 }
 *  }}}
 *
 *  or `{ "version": 1, "error": "…" }` for an invalid option or an internal error. The program may import
 *  the `std/` modules; any other import is reported as missing (E0108). The options are those of
 *  [[Request.read]], as an object or its JSON text. */
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

  /** Makes the current Web Worker answer messages ([[WorkerMain]]); for a worker without a handler of
   *  its own: `importScripts("hugin.js"); Hugin.serveWorker()`. */
  @JSExport def serveWorker(): Unit = WorkerMain.serve()

  /** The compiler's phases in order, for `printAfter`: `[{ "name": …, "description": … }]`. */
  @JSExport def phases(): String = Playground.phases
