package hugin.query

import hugin.core.{Footprint, ProgramElab, Unrecorded, UnrecordedRead}
import hugin.util.DiagnosticRenderer
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** The footprint of an object item (`hugin.core.Footprint`, issue #126, PR 7 step 2) records every read
 *  of its program's declarations: elaborated again under `Unrecorded`, which fails on any read outside
 *  the footprint, every item of the golden programs, the examples and the bench programs elaborates
 *  without failing and to the same result. */
class DeclarationReadsSuite extends munit.FunSuite:
  private def programs: List[Path] =
    List("tests/run", "tests/neg", "tests/pos", "examples", "bench/meta", "bench/small").flatMap { d =>
      val dir = Path.of(d)
      if Files.isDirectory(dir) then Files.list(dir).iterator.asScala.filter(_.toString.endsWith(".hgn")).toList else Nil
    }.sortBy(_.toString)

  private def elaborated(path: String) =
    val db = Database()
    val key = ProgramKey(path, true)
    (db(Signatures, key), db(ObjectItemsOf, key).items.map(_._2))

  /** Runs `body` on a thread with a large stack, as the CLI does (deep programs among the goldens). */
  private def deep(body: => Unit): Unit =
    var failure: Option[Throwable] = None
    val task: Runnable = () =>
      try body
      catch case e: Throwable => failure = Some(e)
    val t = Thread(null, task, "reads", 512L << 20)
    t.start()
    t.join()
    failure.foreach(throw _)

  private def render(r: hugin.core.ElaboratedItem) =
    (r.diagnostics.map(DiagnosticRenderer(color = false).render), r.items.length, r.portable)

  test("every read of the declarations made by an item is in its footprint")(deep {
    var items = 0
    var partial = 0
    for p <- programs do
      val (decls, objects) = elaborated(p.toString)
      for item <- objects do
        val first = ProgramElab.item(decls, item)
        val footprint = first.footprint.nn
        val again =
          try ProgramElab.observed(decls, item, Some(Unrecorded(footprint)))
          catch case e: UnrecordedRead => fail(s"$p: ${item.span.show}: ${e.what}")
        assertEquals(render(again), render(first), s"$p: ${item.span.show}")
        items += 1
        if footprint.globals.size < footprint.ranges.globals.size then partial += 1
    assert(items > 500, items)
    // the footprints are not all of the declarations
    assert(partial > items / 2, s"$partial of $items")
  })

  test("a read missing from a footprint is found") {
    val text = "limit : int = 3.\nother : int = 4.\nsmall : int -> rel.\nsmall N :- N = limit.\n"
    val path = Files.createTempFile("hugin-reads", ".hgn")
    Files.writeString(path, text)
    val (decls, objects) = elaborated(path.toString)
    val first = ProgramElab.item(decls, objects.head)
    val footprint = first.footprint.nn
    assert(footprint.globals.nonEmpty)
    val without = Footprint(footprint.ranges)
    footprint.names.foreach((c, ns) => ns.foreach(without.name(c, _)))
    footprint.whole.foreach(without.all)
    footprint.metas.foreach(without.meta)
    footprint.levels.foreach(without.level)
    footprint.globals.drop(1).foreach(without.global)
    // an `UnrecordedRead` is a control throwable (error recovery does not catch it), which `intercept` passes on
    val caught =
      try
        ProgramElab.observed(decls, objects.head, Some(Unrecorded(without)))
        false
      catch case _: UnrecordedRead => true
    assert(caught)
  }
