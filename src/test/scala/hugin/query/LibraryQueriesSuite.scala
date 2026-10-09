package hugin.query

import hugin.compiler.{Compiler, Settings, SourceLoader, StdlibCache}
import hugin.util.*

/** Libraries as queries: the prelude and the imported files are elaborated as a chain, each file on top of
 *  the files before it (in dependency order), once per database revision and shared by the compilations
 *  whose chains share it; an edit invalidates the edited file and the files after it in the chain, and the
 *  results equal those of a compilation from scratch. */
class LibraryQueriesSuite extends munit.FunSuite:
  private val settings = Settings(printAfter = Set("lower"))
  private val main = "proj/main.hgn"
  private val geo = "proj/lib/geo.hgn"
  private val routes = "proj/lib/routes.hgn"
  private val other = "proj/lib/other.hgn"

  private val files = Map(
    main ->
      """g = %import "lib/geo".
        |r = %import "lib/routes".
        |o = %import "lib/other".
        |%use "std/list".
        |reachable : g.place -> rel.
        |reachable Y :- g.near X, r.legs.path X Y.
        |%output reachable.
        |hops : list g.place -> rel.
        |hops (cons g.here (cons g.there nil)).
        |?- hops L, len L N.
        |""".stripMargin,
    geo ->
      """place : type. here : place. there : place.
        |near : place -> rel.
        |near here.
        |""".stripMargin,
    routes ->
      """geo = %import "geo".
        |%use "std/graph".
        |leg : geo.place -> geo.place -> rel.
        |leg geo.here geo.there.
        |legs = tc { node = geo.place, edge = leg }.
        |""".stripMargin,
    other ->
      """colour : type. red : colour.
        |""".stripMargin
  )

  private def setup(texts: Map[String, String] = files): Database =
    val db = Database()
    texts.foreach((p, t) => db.set(SourceText, p, t))
    db

  /** What a client observes: rendered diagnostics, the printed lowered program, hover in the program. */
  private def observe(path: String)(using db: Database): (List[String], List[String], List[Option[String]]) =
    val key = CompileKey(path, settings)
    val compiled = db(Compile, key)
    val renderer = DiagnosticRenderer(color = false)
    val text = db.get(SourceText, path)
    val offsets = (0 until text.length by 7).toList
    (compiled.diagnostics.map(renderer.render), compiled.printed, offsets.map(o => Ide.hover(key, o)))

  /** The same, compiled from scratch: a new database and, independently, without a database. */
  private def fromScratch(texts: Map[String, String], path: String) =
    val viaDb = observe(path)(using setup(texts))
    // the standard library's parse is the process's shared one (`StdlibCache`), as in `SourceLoader.files`
    val loader: SourceLoader = p => texts.get(p).orElse(SourceLoader.read(p)).map(t => StdlibCache.parsed(p, t))
    val direct = Compiler.compileParsed(loader.load(path).get, settings, loader, _ => ())
    val renderer = DiagnosticRenderer(color = false)
    assertEquals(direct.reporter.sorted.map(renderer.render), viaDb._1, "database and direct compilation differ")
    viaDb

  private def elaborations(using db: Database): Int = db.stats.computedBy("elabLibrary")

  test("the libraries compile as before") {
    given db: Database = setup()
    val compiled = db(Compile, CompileKey(main, settings))
    assert(!compiled.hasErrors, compiled.diagnostics)
    // the prelude after the bundled files it imports
    val std = List("std/reflect", "std/demand").map(m => SourceLoader.StdlibPrefix + m + ".hgn")
    val graph = SourceLoader.StdlibPrefix + "std/graph.hgn"
    val list = SourceLoader.StdlibPrefix + "std/list.hgn"
    assertEquals(compiled.context.unit.libraries.keys.toList, std ++ List(SourceLoader.PreludePath, geo, graph, routes, other, list))
    // the prelude with its imports is one step of the chain
    assertEquals(elaborations, 6)
  }

  test("editing the program does not elaborate the prelude or the libraries again") {
    given db: Database = setup()
    db(Compile, CompileKey(main, settings))
    db.stats.reset()
    db.set(SourceText, main, files(main) + "\nextra : rel.\n")
    db(Compile, CompileKey(main, settings))
    assertEquals(db.stats.computedBy("compile"), 1)
    assertEquals(elaborations, 0)
  }

  test("editing an imported file elaborates it and the files after it in the chain only") {
    given db: Database = setup()
    db(Compile, CompileKey(main, settings))
    db.stats.reset()
    db.set(SourceText, geo, files(geo) + "elsewhere : place.\n")
    db(Compile, CompileKey(main, settings))
    // geo and the files after it (std/graph, routes, other, std/list); not the prelude
    assertEquals(elaborations, 5)
    db.stats.reset()
    db.set(SourceText, other, files(other) + "blue : colour.\n")
    db(Compile, CompileKey(main, settings))
    // other and std/list, after it
    assertEquals(elaborations, 2)
  }

  test("programs sharing a database share the prelude and the libraries they both import") {
    given db: Database = setup(files + ("proj/second.hgn" -> "x = %import \"lib/geo\".\nq : x.place -> rel.\nq x.here.\n"))
    db(Compile, CompileKey(main, settings))
    db.stats.reset()
    val second = db(Compile, CompileKey("proj/second.hgn", settings))
    assert(!second.hasErrors, second.diagnostics)
    assertEquals(elaborations, 0)
    // a program with other settings (no printing) reuses them too
    db(Compile, CompileKey("proj/second.hgn"))
    assertEquals(elaborations, 0)
  }

  test("diagnostics of an imported file are reported once, in its file") {
    val broken = files + (other -> "colour : type.\nbad : colour -> rel.\nbad X :- undefined X.\n")
    given db: Database = setup(broken)
    val diags = db(Compile, CompileKey(main, settings)).diagnostics
    assertEquals(diags.map(_.code).map(_.id), List("E0101"))
    assertEquals(diags.head.primarySpan.source.path, other)
    assertEquals(observe(main), fromScratch(broken, main))
  }

  test("incremental = from scratch under edits of imported files") {
    var texts = files
    given db: Database = setup(texts)
    assertEquals(observe(main), fromScratch(texts, main))
    val edits = List(
      geo -> ("\n(* moved *)\n\n" + files(geo)),
      geo -> (files(geo) + "elsewhere : place.\nnear elsewhere.\n"),
      routes -> files(routes).replace("leg geo.here geo.there.", "leg geo.there geo.here."),
      geo -> files(geo).replace("near here.", "near nowhere."),
      routes -> (files(routes) + "back = %import \"../main\".\n"),
      geo -> files(geo),
      routes -> files(routes),
      other -> "o = %import \"other\".\n",
      other -> files(other)
    )
    for (path, text) <- edits do
      texts = texts.updated(path, text)
      db.set(SourceText, path, text)
      assertEquals(observe(main), fromScratch(texts, main), s"after an edit of $path:\n$text")
  }

  test("cycles: the import closing the cycle is reported where the walk enters it, as from scratch") {
    val cyclic = Map(
      "cy/a.hgn" -> "b = %import \"b\".\nta : type.\n",
      "cy/b.hgn" -> "a = %import \"a\".\ntb : type.\n",
      "cy/p.hgn" -> "a = %import \"a\".\n",
      "cy/q.hgn" -> "b = %import \"b\".\n"
    )
    given db: Database = setup(cyclic)
    val p = observe("cy/p.hgn")
    val q = observe("cy/q.hgn")
    assertEquals(p, fromScratch(cyclic, "cy/p.hgn"))
    assertEquals(q, fromScratch(cyclic, "cy/q.hgn"))
    assert(p._1.exists(_.contains("import cycle: cy/a.hgn -> cy/b.hgn -> cy/a.hgn")), p._1)
    assert(q._1.exists(_.contains("import cycle: cy/b.hgn -> cy/a.hgn -> cy/b.hgn")), q._1)
    // breaking the cycle
    db.set(SourceText, "cy/b.hgn", "tb : type.\n")
    assertEquals(observe("cy/p.hgn"), fromScratch(cyclic.updated("cy/b.hgn", "tb : type.\n"), "cy/p.hgn"))
  }

  test("a missing import is reported until the file appears") {
    val texts = files - other
    given db: Database = setup(texts)
    assertEquals(observe(main), fromScratch(texts, main))
    assert(observe(main)._1.exists(_.contains("cannot find `lib/other`")))
    db.set(SourceText, other, files(other))
    assertEquals(observe(main), fromScratch(files, main))
    db.remove(SourceText, other)
    assertEquals(observe(main), fromScratch(texts, main))
  }
