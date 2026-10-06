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
    assertEquals(s.execute("?- path a X.").output, List("?- path a X.", "X = b.", "X = c."))
  }

  test("an input with errors is rejected and the session is unchanged") {
    val s = session(graph*)
    val before = s.text
    val r = s.execute("path X Y :- edg X Y.")
    assertEquals(errors(r).flatMap(_.code), List("E0101"))
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
    assertEquals(s.execute("?- path d X.").output, List("?- path d X.", "no."))
  }

  test("diagnostics point into the input as typed, with its own lines and columns") {
    val s = session(graph*)
    val input = "reach X :-\n  path a X,\n  goal X."
    val r = s.execute("reach : node -> rel.")
    assertEquals(r.diagnostics, Nil)
    val d = errors(s.execute(input)).head
    assertEquals(d.code, Some("E0101"))
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
    assertEquals(d.code, Some("E0601"))
    val sources = d.labels.map(_.span.source.path).toSet
    assert(sources.subsetOf(Set("<input 2>", "<input 3>")), sources)
  }

  test("warnings are reported for the new input only, once") {
    val s = session(graph*)
    val r = s.execute("from : node -> rel. from X :- edge X Y.")
    assert(!r.hasErrors)
    assertEquals(r.diagnostics.flatMap(_.code), List("W0002"))
    assertEquals(r.diagnostics.head.primarySpan.source.path, "<input 7>")
    assertEquals(s.execute("to : node -> rel. to Y :- edge _ Y.").diagnostics, Nil)
  }

  test("queries are answered once and do not stay in the session") {
    val s = session(graph*)
    val r = s.execute("?- path a c. ?- path c X.")
    assertEquals(r.output, List("?- path a c.", "yes.", "?- path c X.", "no."))
    assert(!s.text.contains("?-"))
    assertEquals(s.execute("edge c a.").output, Nil)
    // a rule and a query in one input: the query sees the rule
    val both = s.execute("loop : node -> rel. loop X :- path X X. ?- loop X.")
    assertEquals(both.output, List("?- loop X.", "X = a.", "X = b.", "X = c."))
  }

  test("a query with errors is rejected") {
    val s = session(graph*)
    val before = s.text
    assertEquals(errors(s.execute("?- path a X, nope X.")).flatMap(_.code), List("E0101"))
    assertEquals(s.text, before)
  }

  test(":type describes symbols through the semantic index") {
    val s = session(graph*)
    assertEquals(s.execute(":type path").output, List("relation path : node -> node -> rel"))
    assertEquals(s.execute(":type node").output, List("object type node"))
    assert(s.execute(":type nothing").hasErrors)
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

  test(":facts loads input facts; invalid facts are rejected") {
    val s = session("node : type. a : node. b : node.", "edge : node -> node -> rel. %input edge.")
    val good = tempFile("e.facts", "edge a b.")
    assertEquals(s.execute(s":facts $good").output, List(s"loaded facts from $good"))
    assertEquals(s.execute("?- edge X Y.").output, List("?- edge X Y.", "X = a, Y = b."))
    val bad = tempFile("bad.facts", "edge a z.")
    assertEquals(errors(s.execute(s":facts $bad")).flatMap(_.code), List("E0801"))
    assertEquals(s.facts, List(good.toString))
  }

  test(":reset starts an empty session") {
    val s = session(graph*)
    assertEquals(s.execute(":reset").output, List("session cleared"))
    assertEquals(s.text, "")
    assertEquals(errors(s.execute("?- path a X.")).flatMap(_.code), List("E0101"))
    assertEquals(s.execute(graph.head).diagnostics, Nil)
  }

  test(":print shows a phase, optionally only the items mentioning a name") {
    val s = session(graph*)
    val all = s.execute(":print records").output
    assert(all.head.contains("after records"))
    assert(all.contains("edge a b."))
    assertEquals(s.execute(":print records path").output.tail, List("path : node -> node -> rel.", "path X Y :- edge X Y.", "path X Z :- edge X Y, path Y Z."))
    assert(s.execute(":print nophase").hasErrors)
  }

  test(":budget, :stats, :explain, :help and :quit") {
    val s = session(graph*)
    assertEquals(s.execute(":stats on").output, List("statistics: on"))
    assert(s.execute("?- path a c.").output.exists(_.startsWith("(* {path}")))
    assertEquals(s.execute(":budget 2").output, List("round budget: 2"))
    assert(s.execute(":budget lots").hasErrors)
    assertEquals(s.execute(":explain e0101").output.head, "E0101: unresolved name")
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

  test("completion offers commands and the names in scope") {
    val s = session(graph*)
    assert(s.completions(Nil).contains(":load"))
    assert(s.completions(Nil).contains("path"))
    assertEquals(s.completions(List(":type")), List("a", "b", "c", "edge", "node", "path"))
    assert(s.completions(List(":print")).contains("lower"))
    assertEquals(s.completions(List(":stats")), List("on", "off"))
  }

  test("session text: chunks keep their offsets; spans map back to the chunk they lie in") {
    val first = Chunk(SourceFile.virtual("<input 1>", "p : rel."), file = false)
    val second = Chunk(SourceFile.virtual("<input 2>", "q : rel.\nq :- r."), file = false)
    val text = SessionText(Vector(first, second))
    assertEquals(text.text, "p : rel.\nq : rel.\nq :- r.")
    assertEquals(text.offsets, Vector(0, 9))
    val session = SourceFile.virtual(SessionText.path, text.text)
    val r = text.text.indexOf("r.")
    val mapped = text.toChunk(Span(session, r, r + 1))
    assertEquals(mapped.source.path, "<input 2>")
    assertEquals((mapped.startLine, mapped.startCol, mapped.text), (1, 5, "r"))
    assertEquals(text.toChunk(Span(session, 2, 5)).source.path, "<input 1>")
    // spans into other files are unchanged
    val other = Span(SourceFile.virtual("f.facts", "x."), 0, 1)
    assertEquals(text.toChunk(other), other)
  }

  test("blanking keeps offsets and line breaks") {
    val c = Chunk(SourceFile.virtual("<input 1>", "p.\n?- p.\nq."), file = false).blank(List((3, 8)))
    assertEquals(c.text, "p.\n     \nq.")
    assertEquals(c.view.content, "p.\n?- p.\nq.")
  }
