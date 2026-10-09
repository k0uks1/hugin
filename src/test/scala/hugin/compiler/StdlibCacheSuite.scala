package hugin.compiler

import hugin.cli.Main
import hugin.core.{ElabBase, GlobalKind}
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** The prelude shared by all compilations of a process ([[StdlibCache]], issue #60): differential tests
 *  of cached against uncached compilation, and a check that compilations do not change the shared base. */
class StdlibCacheSuite extends munit.FunSuite:
  private def goldens: List[Path] =
    List("run", "neg", "pos").flatMap { d =>
      val dir = Path.of("tests", d)
      if Files.isDirectory(dir) then Files.list(dir).iterator.asScala.filter(_.toString.endsWith(".hgn")).toList else Nil
    }.sortBy(_.toString)

  /** Every 6th golden program, and every one that imports a file (a library on top of the prelude). */
  private def sample: List[Path] =
    goldens.zipWithIndex.collect { case (p, i) if i % 6 == 0 || Files.readString(p).contains("%import") => p }

  private def args(p: Path): List[String] =
    val facts = Path.of(p.toString.stripSuffix(".hgn") + ".facts")
    val flags = Path.of(p.toString.stripSuffix(".hgn") + ".flags")
    val extra = if Files.exists(flags) then Files.readString(flags).trim.split("\\s+").filter(_.nonEmpty).toList else Nil
    List("run", p.toString) ++ (if Files.exists(facts) then List("--facts", facts.toString) else Nil) ++ extra :+ "--no-color"

  /** Exit code, standard output and diagnostics of `hugin run`, with the cache on or off. */
  private def run(p: Path, cached: Boolean): (Int, String, String) =
    val before = StdlibCache.enabled
    StdlibCache.enabled = cached
    try
      val out = StringBuilder()
      val err = StringBuilder()
      val code = Main.run(args(p), s => out ++= s += '\n', s => err ++= s += '\n')
      (code, out.toString, err.toString)
    finally StdlibCache.enabled = before

  /** What compilations could change of a base: every mutable field of the core's globals and metas (by
   *  identity: their values are immutable), the numbers of globals, metas, levels, instances and module
   *  instances, and the sizes of the index. */
  private def fingerprint(b: ElabBase): List[Any] =
    val c = b.core
    val globals = c.globals.toList.map(g => (g.ty, g.tyTm, g.kind, g.pending)).map(_.productIterator.map(System.identityHashCode).toList)
    val metas = c.metas.toList.map(m => (m.solution.map(System.identityHashCode), m.allowUnsolved))
    val idx = b.index
    List(
      globals,
      metas,
      c.levels.snapshot(),
      c.instances,
      c.moduleInstances.length,
      List(idx.references.length, idx.variables.length, idx.staging.length, idx.instances.length, idx.symbols.length, idx.scopes.length),
      b.items.length,
      b.diagnostics
    )

  private def sharedPrelude(): ElabBase =
    StdlibCache.prelude(StdlibCache.bundledChain(), builtinNames = true)

  test("compilations with the shared prelude give exactly the output of compilations without it") {
    for p <- sample do assertEquals(run(p, cached = true), run(p, cached = false), p.toString)
  }

  test("compilations do not change the shared prelude") {
    val base = sharedPrelude()
    val before = fingerprint(base)
    for p <- sample do run(p, cached = true)
    assert(sharedPrelude() eq base, "the prelude was elaborated again")
    assertEquals(fingerprint(base), before)
  }

  test("the prelude is elaborated once per text: an edited prelude is elaborated, and served from then on") {
    val text = SourceLoader.stdlib(SourceLoader.PreludePath).get + "\nextra_rel : int -> rel.\n"
    val chain = StdlibCache.bundledChain(text)
    val count = StdlibCache.elaborations
    val base = StdlibCache.prelude(chain, builtinNames = true)
    assertEquals(StdlibCache.elaborations, count + 1)
    assert(StdlibCache.prelude(StdlibCache.bundledChain(text), builtinNames = true) eq base)
    assert(base.prelude.contains("extra_rel"))
    assert(!sharedPrelude().prelude.contains("extra_rel"))
    // a parse that is not the cache's own (other positions) is never given the shared base
    val other = Parsed(hugin.util.SourceFile.virtual(SourceLoader.PreludePath, text))
    assert(StdlibCache.prelude(chain.init :+ other, builtinNames = true) ne base)
  }

  test("the uncached prelude elaborates to the same globals as the shared one") {
    val shared = sharedPrelude()
    def items(p: Parsed) =
      hugin.core.SourceItems(p.source.path, "", Parsed(hugin.util.SourceFile.virtual(p.source.path, p.source.content)).program.items)
    val chain = StdlibCache.bundledChain()
    val fresh = hugin.core.ProgramElab.preludeChain(chain.init.map(items), items(chain.last), builtinNames = true)
    def shape(b: ElabBase) = b.core.globals.toList.map { g =>
      val kind = g.kind match
        case GlobalKind.Definition(tm, _) => s"definition $tm"
        case other => other.toString
      (g.name, g.tyTm.toString, kind, g.span.show)
    }
    assertEquals(shape(fresh), shape(shared))
    assertEquals(fresh.prelude, shared.prelude)
    assertEquals(fresh.diagnostics.map(_.message), shared.diagnostics.map(_.message))
  }
