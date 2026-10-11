package hugin.web

import hugin.ide.{Annotations, Target}
import hugin.query.Database
import hugin.util.diagnostics.Json

/** The query database of the browser build, kept for the lifetime of the page or worker
 *  (`docs/design/web-ide.md`, 5.1). The program is the `SourceText` input of its file: a request with the
 *  same text as the previous one reuses the memoised compilation (setting an equal input starts no new
 *  revision), so an `analyse` after a `check`, or a repeated request, costs no compilation. A request that
 *  fails with an internal error starts a new database, as a restarted worker does. */
object Session:
  private var database: Database = Database()

  def db: Database = database

  /** Drops the database (after an internal error, whose memos are not trusted). */
  def reset(): Unit = database = Database()

  /** The annotation table of the program (`hugin.ide.Annotations`) as the playground reads it:
   *
   *  {{{
   *  { "names": [[from, to, hover, group, flags, target], …],
   *    "hovers": [[signature, note, …], …],
   *    "hints": [[at, label, tooltip, kind], …] }
   *  }}}
   *
   *  Offsets are UTF-16 code units, as CodeMirror's positions. `hover` indexes `hovers` (null if hover shows
   *  nothing there); `flags` bit 0 marks a declaration; `target` is absent, the offset of the declaration
   *  in the program, or `[module, name]` for a declaration of the bundled standard library
   *  (`["std/graph", "tc"]`). A hover is its signature (null if it has none) followed by its notes. `kind`
   *  is `staging`, `implicit` or `level`. */
  def info(a: Annotations, file: String): Json =
    val names = a.names.map { n =>
      val target = n.target.collect {
        case Target.InFile(sp) if sp.source.path == file => Json.num(sp.start.toLong)
        case Target.Library(module, name) => Json.Arr(List(Json.str(module), Json.str(name)))
      }
      Json.Arr(
        List(
          Json.num(n.span.start.toLong),
          Json.num(n.span.end.toLong),
          if n.hover < 0 then Json.Null else Json.num(n.hover.toLong),
          Json.num(n.group.toLong),
          Json.num(if n.declaration then 1 else 0)
        ) ++ target
      )
    }
    val hovers = a.hovers.toList.map(h => Json.Arr(h.signature.fold(Json.Null)(Json.str) :: h.notes.map(Json.str)))
    val hints = a.hints.map { h =>
      Json.Arr(List(Json.num(h.at.start.toLong), Json.str(h.label), Json.str(h.tooltip), Json.str(h.kind.toString.toLowerCase)))
    }
    Json.obj("names" -> Json.Arr(names), "hovers" -> Json.Arr(hovers), "hints" -> Json.Arr(hints))
