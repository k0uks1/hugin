package hugin.ide

import hugin.compiler.SymKind
import hugin.query.{CompileKey, Database, SourceText}

/** The editor features of [[hugin.ide]] (issue #147), in offsets: what the language server encodes for the
 *  protocol (`hugin.lsp`, `tests/lsp`), asserted on the shared layer the browser build calls too. */
class FeaturesSuite extends munit.FunSuite:
  private val path = "p.hgn"

  /** The program `text` as the file `file` of the database. */
  private def program(text: String, file: String = path)(using db: Database): CompileKey =
    db.set(SourceText, file, text)
    CompileKey(file)

  /** The offset of the `n`-th occurrence of `needle` in `text`, plus `shift`. */
  private def at(text: String, needle: String, shift: Int = 0, n: Int = 0): Int =
    Iterator.iterate(text.indexOf(needle))(i => text.indexOf(needle, i + 1)).drop(n).next() + shift

  private val graph =
    """graph : Type = { node : type, edge : node -> node -> rel }.
      |tc (g : graph) = {
      |  path : g.node -> g.node -> rel.
      |  path X Y :- g.edge X Y.
      |  path X Z :- g.edge X Y, path Y Z.
      |}.
      |city : type. berlin : city. paris : city.
      |road : city -> city -> rel.
      |%input road.
      |roads = tc { node = city, edge = road }.
      |%output roads.path.
      |""".stripMargin

  private val nat = "nat : Type.\nzero : nat.\nsuc : nat -> nat.\n"

  test("hover: the signature, then the notes; nothing between tokens on the meta level") {
    given Database = Database()
    val key = program(graph)
    assertEquals(Hover.at(key, at(graph, "roads.path", 7)).flatMap(_.signature), Some("relation roads.path : city -> city -> rel"))
    assertEquals(Hover.at(key, at(graph, "X Y :-")).flatMap(_.signature), Some("variable X : city"))
    // the meta level's notes: the type and stage of the expression
    val text = "ident : A -> A = [x] x.\nthree : int = ident 3.\ncode : ⇑int = 4.\n"
    val key2 = program(text, "p2.hgn")
    assertEquals(
      Hover.at(key2, at(text, "4.")),
      Some(Hover(None, List("`4` : `⇑int`  \nstage: meta, object code `⇑int`", "elaborated: `⟨4⟩`")))
    )
    assertEquals(Hover.at(key2, at(text, "\nthree")), None)
  }

  test("hover: offsets are UTF-16 code units, also after characters outside the Basic Multilingual Plane") {
    val text = "(* 𝔾 *) city : type.\nlives : city -> rel.\n"
    given Database = Database()
    val key = program(text)
    assertEquals(Hover.at(key, at(text, "city ->")).flatMap(_.signature), Some("object type city : type"))
  }

  test("navigation: a declaration in the file, a library declaration, references with and without it") {
    given Database = Database()
    val key = program(graph)
    val use = at(graph, "road }")
    assertEquals(Navigation.definition(key, use).collect { case Target.InFile(sp) => sp.start }, Some(at(graph, "road :")))
    val refs = Navigation.references(key, use, includeDeclaration = true).map(_.start)
    assertEquals(refs, List(at(graph, "road :"), at(graph, "road."), use))
    assertEquals(Navigation.references(key, use, includeDeclaration = false).map(_.start), refs.tail)
    val text = "%use \"std/graph\".\ncity : type.\nroad : city -> city -> rel.\n%input road.\nroads = tc { node = city, edge = road }.\n"
    val key2 = program(text, "p2.hgn")
    assertEquals(Navigation.definition(key2, at(text, "tc")), Some(Target.Library("std/graph", "tc")))
  }

  test("completion: the prefix being typed, the candidates' kinds, the ranking by the expected type") {
    val text = nat + "size : nat -> int.\nsize zero = 0.\nsize (suc M) = 1.\nquad : nat -> nat.\nquad Nat = s.\n"
    given Database = Database()
    val key = program(text)
    val off = at(text, "= s.", 3)
    val cs = Completion.at(key, off)
    assertEquals(cs.from, off - 1)
    assert(cs.ranked)
    val byLabel = cs.items.map(c => c.label -> c).toMap
    assertEquals(byLabel("suc").kind, CandidateKind.MetaDefinition)
    assert(byLabel("suc").fits)
    assert(!byLabel("size").fits)
    assertEquals(Completion.triggers, List(".", "{", "%"))
  }

  test("completion: object syntax only inside a quote, meta values after `$`") {
    assertEquals(Completion.inQuote("x = '(p X", 9), Some(false))
    assertEquals(Completion.inQuote("x = '(p $v", 10), Some(true))
    assertEquals(Completion.inQuote("x = (p X", 8), None)
  }

  test("fixes: a diagnostic's suggestion, preferred, with its edit in offsets") {
    val text = "p : int -> rel.\np X :- p Y.\n"
    given Database = Database()
    val key = program(text)
    val fixes = Fixes.at(key, path, 0, text.length)
    assert(fixes.nonEmpty, fixes)
    val f = fixes.head
    assertEquals(f.kind, FixKind.QuickFix)
    assert(f.diagnostic.isDefined)
    assert(f.edits.forall(e => e.span.source.path == path && e.span.start >= 0 && e.span.end <= text.length), f.edits)
  }

  test("fixes: split, add the missing clauses, start the clauses, refine a hole") {
    val split = nat + "double : nat -> nat.\ndouble N = suc (suc N).\n"
    given Database = Database()
    val key = program(split)
    val s = Fixes.at(key, path, at(split, "N = suc"), at(split, "N = suc")).find(_.title == "Split on `N`").get
    assertEquals(s.kind, FixKind.Rewrite)
    assertEquals(s.edits.map(_.text), List("double zero = suc (suc zero).\ndouble (suc N1) = suc (suc (suc N1))."))
    val missing = nat + "both : nat -> nat -> nat.\nboth (suc M) (suc N) = M.\n"
    val key2 = program(missing, "p2.hgn")
    val d = Diagnostics.all(key2).find(_.code.id == "E0911").get
    val add = Fixes.at(key2, key2.path, d.primarySpan.start, d.primarySpan.start).find(_.title.startsWith("Add the")).get
    assert(add.preferred)
    assertEquals(add.edits.map(e => (e.span.start, e.text)), List((at(missing, "M.", 2), "\nboth zero _ = ?.\nboth (suc _) zero = ?.")))
    val decl = nat + "size : nat -> int.\n"
    val key3 = program(decl, "p3.hgn")
    assertEquals(Fixes.at(key3, key3.path, at(decl, "size"), at(decl, "size")).map(_.title), List("Add a clause for `size`"))
    val hole = nat + "double : nat -> nat.\ndouble N = ?.\n"
    val key4 = program(hole, "p4.hgn")
    val refine = Fixes.at(key4, key4.path, at(hole, "?"), at(hole, "?")).filter(_.title.startsWith("Refine")).map(_.edits.map(_.text))
    assertEquals(refine, List(List("zero"), List("(suc ?)")))
  }

  test("outline: declarations nested by their module bodies, the extent covering the children") {
    given Database = Database()
    val key = program(graph)
    val nodes = Outline.of(key)
    val tc = nodes.find(_.symbol.name == "tc").get
    assertEquals(tc.children.map(_.symbol.name), List("path"))
    assertEquals(tc.children.head.symbol.kind, SymKind.Rel)
    assert(tc.extent.start <= tc.children.head.extent.start && tc.children.head.extent.end <= tc.extent.end)
    assert(!nodes.exists(_.symbol.name == "path"))
  }

  test("hints, goals and the expansion") {
    val text = "ident : A -> A = [x] x.\nthree : int = ident 3.\nk : Type = int.\n"
    given Database = Database()
    val key = program(text)
    assertEquals(Hints.in(key, path, 0, text.length, HintSettings(levels = true)).map(_.label), List("{int}", "₀"))
    assertEquals(Hints.in(key, path, 0, text.length, HintSettings(implicits = false, levels = true)).map(_.label), List("₀"))
    val hole = nat + "double : nat -> nat.\ndouble N = suc ?d.\n"
    val key2 = program(hole, "p2.hgn")
    val d = Diagnostics.all(key2).find(_.code.id == "E0924").get
    val g = Goals.of(key2, d).get
    assertEquals((g.tpe, g.name, g.context), ("nat", Some("d"), List(("N", "nat"))))
    val staged =
      "p : int -> rel.\n%input p.\nq : int -> rel.\nmk (r : int -> rel) = { s : int -> rel. s X :- r X. }.\nm = mk p.\n%output m.s.\n"
    val key3 = program(staged, "p3.hgn")
    val sites = Expansions.sites(key3, key3.path)
    assertEquals(sites.map((sp, n) => (sp.text, n)), List(("mk p", 1)))
    assert(Expansions.at(key3, sites.head._1.start).exists(_.contains("m.s X :- p X.")), Expansions.at(key3, sites.head._1.start))
  }

  test("a facts file: syntax diagnostics only, no other feature") {
    val db = Database()
    db.set(SourceText, "in.facts", "edge(1, 2).\nedge(2,\n")
    given Database = db
    val key = CompileKey("in.facts")
    assert(Diagnostics.all(key).nonEmpty)
    assertEquals(Hover.at(key, 1), None)
    assertEquals(Completion.at(key, 1).items, Nil)
    assertEquals(Outline.of(key), Nil)
    assertEquals(Fixes.at(key, "in.facts", 0, 5), Nil)
  }
