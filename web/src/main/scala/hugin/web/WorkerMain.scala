package hugin.web

import scala.scalajs.js
import scala.util.control.NonFatal

/** The Web Worker entry, [[Hugin.serveWorker]]: after `importScripts("hugin.js"); Hugin.serveWorker()` in a
 *  classic worker (or the same with `hugin.mjs` in a module worker) the worker answers messages
 *
 *  {{{
 *  { id, op: "check" | "run", source: "…", options: { … } }   →   { id, result: { …the JSON of Hugin… } }
 *  { id, op: "phases" }                                       →   { id, result: [ … ] }
 *  }}}
 *
 *  and posts `{ ready: true }` at once. A worker computes one request at a time: to cancel a request or to
 *  enforce a time budget, the page terminates the worker and starts a new one. (The playground's own
 *  site/play/worker.js has a handler of its own and calls [[Hugin]] directly.) */
object WorkerMain:
  def serve(): Unit =
    val self = js.Dynamic.global.globalThis
    val handler: js.Function1[js.Dynamic, Unit] = event => self.postMessage(answer(event.data))
    self.onmessage = handler
    self.postMessage(js.Dynamic.literal(ready = true))

  private def answer(request: js.Dynamic): js.Any =
    val id = request.id
    try
      val op = request.op.asInstanceOf[Any]
      val options = request.options.asInstanceOf[js.UndefOr[js.Any]]
      def source = request.source.asInstanceOf[Any] match
        case s: String => s
        case _ => throw IllegalArgumentException("`source` must be a string")
      val json = op match
        case "check" => Hugin.check(source, options)
        case "run" => Hugin.run(source, options)
        case "phases" => Hugin.phases()
        case _ => throw IllegalArgumentException(s"unknown op `$op`; expected check, run or phases")
      js.Dynamic.literal(id = id, result = js.JSON.parse(json))
    catch case NonFatal(e) => js.Dynamic.literal(id = id, result = js.Dynamic.literal(version = Playground.Version, error = e.getMessage))
