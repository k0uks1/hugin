package hugin.repl

import hugin.util.*
import java.nio.file.{Files, Path}

class SessionSuite extends munit.FunSuite:
  private val graph = List(
    "node : type. a : node. b : node. c : node.",
    "edge : node -> node -> rel.",
    "edge a b. edge b c.",
    "path : node -> node -> rel.",
    "path X Y :- edge X Y.",
    "path X Z :- edge X Y, path Y Z."
  )

  private def session(inputs: String*): Session =
    val s = Session()
    for i <- inputs do
      val r = s.execute(i)
      assert(!r.hasErrors, s"unexpected errors for `$i`: ${r.diagnostics.map(_.message)}")
    s

  private def errors(r: Reply): List[Diagnostic] = r.diagnostics.filter(_.severity == Severity.Error)

  private def tempFile(name: String, text: String): Path =
    val dir = Files.createTempDirectory("hugin-repl")
    Files.writeString(dir.resolve(name), text)

  test("declarations and rules are accepted one by one") {
    val s = Session()
    for i <- graph do assertEquals(s.execute(i), Reply(), i)
    assertEquals(s.text, graph.mkString("\n"))
    assertEquals(s.execute("?- path a X.").output, List("X = b.", "X = c."))
  }

  test("an input with errors is rejected and the session is unchanged") {
    val s = session(graph*)
    val before = s.text
    val r = s.execute("path X Y :- edg X Y.")
    assertEquals(errors(r).flatMap(_.code).map(_.id), List("E0101"))
    assertEquals(s.text, before)
    // the rejected rule did not become part of the session: the corrected one is accepted
    assertEquals(s.execute("path X Y :- edge Y X.").diagnostics, Nil)
  }

  test("several items on one line are accepted or rejected together") {
    val s = session(graph*)
    val before = s.text
    assert(s.execute("d : node. edge c d. edge d e.").hasErrors)
    assertEquals(s.text, before)
    assertEquals(s.execute("d : node. edge c d.").diagnostics, Nil)
    assertEquals(s.execute("?- path d X.").output, List("no."))
  }

  test("diagnostics point into the input as typed, with its own lines and columns") {
    val s = session(graph*)
    val input = "reach X :-\n  path a X,\n  goal X."
    val r = s.execute("reach : node -> rel.")
    assertEquals(r.diagnostics, Nil)
    val d = errors(s.execute(input)).head
    assertEquals(d.code.map(_.id), Some("E0101"))
    val span = d.primarySpan
    assertEquals(span.source.path, "<input 8>")
    assertEquals(span.source.content, input)
    assertEquals((span.startLine, span.startCol), (2, 2))
    assertEquals(span.text, "goal")
    assert(DiagnosticRenderer(false).render(d).contains(" --> <input 8>:3:3\n"))
  }

  test("errors caused by an input in earlier text point to the earlier input") {
    val s = session("p : rel. q : rel.", "p :- q.")
    val d = errors(s.execute("q :- not p.")).head
    assertEquals(d.code.map(_.id), Some("E0601"))
    val sources = d.labels.map(_.span.source.path).toSet
    assert(sources.subsetOf(Set("<input 2>", "<input 3>")), sources)
  }

  test("warnings are reported for the new input only, once") {
    val s = session(graph*)
    val r = s.execute("never : node -> prop.")
    assert(!r.hasErrors)
    assertEquals(r.diagnostics.flatMap(_.code).map(_.id), List("W0005"))
    assertEquals(r.diagnostics.head.primarySpan.source.path, "<input 7>")
    assertEquals(s.execute("to : node -> rel. to Y :- edge _ Y.").diagnostics, Nil)
  }

  test("unused definitions are not reported: later inputs use them") {
    val s = session(graph*)
    assertEquals(s.execute("start : node = a.").diagnostics, Nil)
    assertEquals(s.execute("?- path start X.").output, List("X = b.", "X = c."))
  }

  test("repeated variables in one atom") {
    val s = session(graph*)
    s.execute("edge c a.")
    assertEquals(s.execute("?- path X X.").output, List("X = a.", "X = b.", "X = c."))
  }

  test("queries are answered once and do not stay in the session; several are headed by the query") {
    val s = session(graph*)
    val r = s.execute("?- path a c. ?- path c X.")
    assertEquals(r.output, List("?- path a c.", "yes.", "?- path c X.", "no."))
    assert(!s.text.contains("?-"))
    assertEquals(s.execute("edge c a.").output, Nil)
    // a rule and a query in one input: the query sees the rule
    val both = s.execute("loop : node -> rel. loop X :- path X X. ?- loop X.")
    assertEquals(both.output, List("X = a.", "X = b.", "X = c."))
  }

  test("a query with errors is rejected") {
    val s = session(graph*)
    val before = s.text
    assertEquals(errors(s.execute("?- path a X, nope X.")).flatMap(_.code).map(_.id), List("E0101"))
    assertEquals(s.text, before)
  }

  test(":type shows the type of names, module paths, meta expressions and object terms") {
    val s = session(graph*)
    // the session's `path` shadows the one of the prelude's `tc`
    assertEquals(s.execute(":type path").output, List("relation path : node -> node -> rel"))
    assertEquals(s.execute(":type a").output, List("constructor a : node"))
    assertEquals(s.execute(":type cons a nil").output, List("cons a nil : cons[node]"))
    assertEquals(s.execute(":type 1 + 2").output, List("1 + 2 : int"))
    assertEquals(s.execute("g = tc { node = node, edge = edge }.").diagnostics, Nil)
    assertEquals(s.execute(":type g.path").output, List("relation g.path : node -> node -> rel"))
    assertEquals(
      s.execute(":type tc { node = node, edge = edge }").output,
      List("tc { node = node, edge = edge } : { path : ⇑(node -> node -> rel) }")
    )
    val d = errors(s.execute(":type cons nothing nil")).head
    assertEquals(d.code.map(_.id), Some("E0101"))
    assertEquals((d.primarySpan.source.path, d.primarySpan.start, d.primarySpan.text), ("<input>", 5, "nothing"))
    // probes do not change the session
    assertEquals(s.execute(":type nothing").diagnostics.flatMap(_.code).map(_.id), List("E0101"))
    assert(!s.text.contains("repl"))
  }

  test(":kind and :list") {
    val s = session(graph*)
    assertEquals(s.execute(":kind node").output, List("node : object type"))
    assertEquals(s.execute(":kind edge").output, List("edge : relation"))
    s.execute("?- path a b.")
    assertEquals(s.execute(":list").output, graph)
    assertEquals(Session().execute(":list").output, List("(* the session is empty *)"))
  }

  test(":load adds a file; its diagnostics point into the file") {
    val file = tempFile("g.hgn", graph.mkString("\n") + "\n?- path b X.\n")
    val s = Session()
    val r = s.execute(s":load $file")
    assertEquals(r.output, List(s"loaded $file", "?- path b X.", "X = c."))
    assertEquals(s.execute("?- path a c.").output.last, "yes.")
    assert(s.execute(s":load $file").hasErrors, "loading a file twice")
    val bad = tempFile("bad.hgn", "x : rel.\nx :- y.\n")
    val d = errors(s.execute(s":load $bad")).head
    assertEquals(d.primarySpan.source.path, bad.toString)
    assertEquals(d.primarySpan.startLine, 1)
    assert(s.execute(":load no/such/file.hgn").hasErrors)
  }

  test(":reload reads changed files again") {
    val file = tempFile("g.hgn", graph.mkString("\n"))
    val s = Session()
    s.load(file.toString)
    Files.writeString(file, graph.mkString("\n") + "\nedge c a.")
    assertEquals(s.execute(":reload").output, List("reloaded 1 file(s)"))
    assertEquals(s.execute("?- path c a.").output.last, "yes.")
  }

  /** A directory with the given files (relative paths, created with their parents). */
  private def tempDir(files: (String, String)*): Path =
    val dir = Files.createTempDirectory("hugin-repl")
    for (name, text) <- files do
      Files.createDirectories(dir.resolve(name).getParent)
      Files.writeString(dir.resolve(name), text)
    dir

  private val geo = "place : type. here : place. there : place.\n"

  test("a loaded file keeps its path: its imports resolve relative to it, its diagnostics point into it") {
    val dir = tempDir(
      "lib/geo.hgn" -> geo,
      "main.hgn" -> "g = %import \"lib/geo\".\nat : g.place -> rel.\nat g.here.\n",
      "bad.hgn" -> "(* line 1 *)\nx = %import \"lib/nowhere\".\n"
    )
    val s = Session()
    assertEquals(s.load(dir.resolve("main.hgn").toString).diagnostics, Nil)
    assertEquals(s.execute("?- at X.").output, List("X = geo.here."))
    assertEquals(s.imports, List(dir.resolve("lib/geo.hgn").toString))
    // an input imports relative to the working directory
    assertEquals(errors(s.execute("y = %import \"lib/geo\".")).flatMap(_.notes), List("resolved to `lib/geo.hgn`"))
    val d = errors(s.load(dir.resolve("bad.hgn").toString)).head
    assertEquals(d.code.map(_.id), Some("E0108"))
    assertEquals(
      (d.primarySpan.source.path, d.primarySpan.startLine, d.primarySpan.text),
      (dir.resolve("bad.hgn").toString, 1, "\"lib/nowhere\"")
    )
    assertEquals(d.notes, List(s"resolved to `${dir.resolve("lib/nowhere.hgn")}`"))
    assertEquals(s.execute(":list").output, List(s"(* loaded ${dir.resolve("main.hgn")} *)"))
  }

  test(":reload reads the files imported by loaded files again, transitively") {
    val dir = tempDir(
      "base.hgn" -> geo,
      "lib.hgn" -> "b = %import \"base\".\nnear : b.place -> rel.\nnear b.here.\n",
      "main.hgn" -> "l = %import \"lib\".\n"
    )
    val s = Session()
    s.load(dir.resolve("main.hgn").toString)
    assertEquals(s.execute("?- l.near X.").output, List("X = base.here."))
    assertEquals(s.imports.map(Path.of(_).getFileName.toString), List("base.hgn", "lib.hgn"))
    Files.writeString(dir.resolve("base.hgn"), geo + "elsewhere : place.\n")
    Files.writeString(dir.resolve("lib.hgn"), "b = %import \"base\".\nnear : b.place -> rel.\nnear b.here. near b.elsewhere.\n")
    assertEquals(s.execute(":reload").output, List("reloaded 3 file(s)"))
    assertEquals(s.execute("?- l.near X.").output, List("X = base.elsewhere.", "X = base.here."))
    // a reload with errors in an imported file is rejected: the session keeps the files as they were
    Files.writeString(dir.resolve("base.hgn"), "place : typ.\n")
    assertEquals(errors(s.execute(":reload")).flatMap(_.code).map(_.id).distinct, List("E0101"))
    assertEquals(s.execute("?- l.near X.").output, List("X = base.elsewhere.", "X = base.here."))
    // a file imported only by the reloaded text is read too
    Files.writeString(dir.resolve("base.hgn"), geo + "elsewhere : place.\n")
    Files.writeString(dir.resolve("extra.hgn"), "more : rel. more.\n")
    Files.writeString(dir.resolve("main.hgn"), "l = %import \"lib\".\ne = %import \"extra\".\n")
    assertEquals(s.execute(":reload").diagnostics.map(_.message), Nil)
    assertEquals(s.execute("?- e.more.").output, List("yes."))
  }

  test(":facts loads input facts; invalid facts are rejected") {
    val s = session("node : type. a : node. b : node.", "edge : node -> node -> rel. %input edge.")
    val good = tempFile("e.facts", "edge a b.")
    assertEquals(s.execute(s":facts $good").output, List(s"loaded facts from $good"))
    assertEquals(s.execute("?- edge X Y.").output, List("X = a, Y = b."))
    val bad = tempFile("bad.facts", "edge a z.")
    assertEquals(errors(s.execute(s":facts $bad")).flatMap(_.code).map(_.id), List("E0801"))
    assertEquals(s.facts, List(good.toString))
  }

  test(":reset starts an empty session") {
    val s = session(graph*)
    assertEquals(s.execute(":reset").output, List("session cleared"))
    assertEquals(s.text, "")
    assertEquals(errors(s.execute("?- path a X.")).flatMap(_.code).map(_.id), List("E0101"))
    assertEquals(s.execute(graph.head).diagnostics, Nil)
  }

  test(":print shows a phase, optionally only the items mentioning a name") {
    val s = session(graph*)
    val all = s.execute(":print records").output
    assert(all.head.contains("after records"))
    assert(all.contains("edge a b."))
    assertEquals(
      s.execute(":print records path").output.tail,
      List("path : node -> node -> rel.", "path X Y :- edge X Y.", "path X Z :- edge X Y, path Y Z.")
    )
    assert(s.execute(":print nophase").hasErrors)
  }

  test("aliases: :hover for :type, :print-after for :print; :imports") {
    val s = session(graph*)
    assertEquals(s.execute(":hover path").output, s.execute(":type path").output)
    assertEquals(s.execute(":print-after records path").output, s.execute(":print records path").output)
    assertEquals(s.execute(":hover").diagnostics.head.message, "usage: :hover <expr>")
    assertEquals(s.complete(":ho", 3), List(":hover"))
    assert(s.complete(":print-after ", 13).contains("lower"))
    assert(s.execute(":help").output.exists(_.endsWith("(also :hover)")))
    assertEquals(s.execute(":imports").output, List("(* the session imports no files *)"))
    assertEquals(Session().execute(":hovr x").diagnostics.head.helps.head, "did you mean `:hover`?")
  }

  test(":stats, :explain, :help and :quit") {
    val s = session(graph*)
    assertEquals(s.execute(":stats on").output, List("statistics: on"))
    assert(s.execute("?- path a c.").output.exists(_.startsWith("(* {path}")))
    assert(s.execute(":budget 2").hasErrors) // removed with %partial
    assertEquals(s.execute(":explain e0101").output.head, "# E0101: unresolved name")
    assert(s.execute(":help").output.exists(_.contains(":print <phase> [<name>]")))
    assert(s.execute(":quit").quit)
  }

  test("unknown commands list the commands and suggest a similar one") {
    val d = Session().execute(":lod x").diagnostics.head
    assertEquals(d.message, "unknown command `:lod`")
    assertEquals(d.helps.head, "did you mean `:load`?")
    assert(d.helps.last.contains(":load :reload :facts"))
    assertEquals(Session().execute(":load").diagnostics.head.message, "usage: :load <file.hgn>")
  }

  test("completion offers commands, their arguments and the names in scope at the cursor") {
    val s = session(graph*)
    assertEquals(s.complete(":lo", 3), List(":load"))
    assertEquals(s.complete(":stats ", 7), List("on", "off"))
    assert(s.complete(":print ", 7).contains("lower"))
    assert(s.complete(":type ", 6).containsSlice(List("edge")))
    assertEquals(s.complete("?- pa", 5), List("pair", "path")) // `pair` is from the prelude
    assertEquals(s.complete("p X :- ed", 9), List("edge"))
    // members of a module
    s.execute("g = tc { node = node, edge = edge }.")
    assertEquals(s.complete("?- g.", 5), List("path"))
    assertEquals(s.complete("?- g.pa", 7), List("path"))
    assertEquals(s.complete("%inp", 4), List("input"))
    // the variables of the rule being typed, which does not compile yet
    assertEquals(s.complete("p Xa :- edge Xa Yb, path Y", 26), List("Yb"))
    assertEquals(s.complete("p Xa :- edge Xa Yb,\n  path (X", 29), List("Xa"))
    // ... and not those of the previous item
    assertEquals(s.complete("p Xa. q Yb :- edge Yb X", 23), Nil)
    // completion does not change the session
    assertEquals(s.complete("?- pat", 6), List("path"))
    assert(!s.text.contains("?-"))
  }

  test("blanking keeps offsets and line breaks") {
    val c = Chunk("<input 1>", "p.\n?- p.\nq.", file = false).blank(List((3, 8)))
    assertEquals(c.text, "p.\n     \nq.")
  }

  test("queries and probes are elaborated as extra items: the session's items are not elaborated again") {
    val s = session(graph*)
    val db = s.database
    def elaborated = db.stats.computedBy("elabItem")
    def signatures = db.stats.computedBy("signatures")
    db.stats.reset()
    assertEquals(s.execute("?- path a X.").output, List("X = b.", "X = c."))
    assertEquals((elaborated, signatures), (1, 0)) // the query
    db.stats.reset()
    assertEquals(s.execute(":type path").output, List("relation path : node -> node -> rel"))
    assertEquals(elaborated, 0) // the probe is a definition, elaborated with the declarations
    db.stats.reset()
    assertEquals(s.execute(":type cons a nil").output, List("cons a nil : cons[node]"))
    assertEquals(elaborated, 1) // the object probe `?- It'repl = cons a nil.`
    db.stats.reset()
    assertEquals(s.complete("?- pat", 6), List("path"))
    assertEquals(elaborated, 1)
    // probes leave the session as it was: a new input elaborates its own items only
    db.stats.reset()
    assertEquals(s.execute("r : node -> rel. r X :- path a X."), Reply())
    assertEquals(elaborated, 1)
    assertEquals(s.execute("?- r X.").output, List("X = b.", "X = c."))
    assertEquals(db.stats.computedBy("elabLibrary"), 0)
  }

  test("the prelude and imported files are elaborated once for the whole session") {
    val lib = tempFile("geo.hgn", "place : type. here : place.\n")
    val s = Session()
    s.execute(s"g = %import \"${lib.toString.replace("\\", "/")}\".")
    val db = s.database
    assertEquals(db.stats.computedBy("elabLibrary"), 2)
    db.stats.reset()
    for i <- graph do assertEquals(s.execute(i), Reply(), i)
    assertEquals(s.execute("?- path a X.").output, List("X = b.", "X = c."))
    assert(db.stats.computedBy("compile") > 0)
    assertEquals(db.stats.computedBy("elabLibrary"), 0)
    assertEquals(db.stats.computedBy("nameLibrary"), 0)
  }
