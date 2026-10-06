package hugin.query

class CompilerQueriesSuite extends munit.FunSuite:
  private val program =
    """graph : mod = { node : type, edge : node -> node -> rel }.
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

  private val key = CompileKey("p.hgn")

  private def setup(): Database =
    val db = Database()
    db.set(SourceText, "p.hgn", program)
    db.set(SourceText, "f.facts", "road berlin paris.")
    db

  /** Offset of the `n`-th occurrence (0-based) of `needle`. */
  private def at(needle: String, n: Int = 0): Int =
    Iterator.iterate(program.indexOf(needle))(i => program.indexOf(needle, i + 1)).drop(n).next()

  test("editing a facts file re-evaluates without recompiling") {
    given db: Database = setup()
    val ek = EvaluateKey(key, List("f.facts"))
    assertEquals(db(Evaluate, ek).result.map(_.output), Some(List("roads.path berlin paris.")))
    db.stats.reset()
    db.set(SourceText, "f.facts", "road paris berlin.")
    assertEquals(db(Evaluate, ek).result.map(_.output), Some(List("roads.path paris berlin.")))
    assertEquals(db.stats.computedBy("compile"), 0)
    assertEquals(db.stats.computedBy("evaluate"), 1)
  }

  test("editing the program recompiles; an unchanged revision reuses everything") {
    given db: Database = setup()
    db(Evaluate, EvaluateKey(key, List("f.facts")))
    db.stats.reset()
    db(Evaluate, EvaluateKey(key, List("f.facts")))
    assertEquals(db.stats.computed, 0)
    db.set(SourceText, "p.hgn", program + "\nextra : rel.\n")
    db(Evaluate, EvaluateKey(key, List("f.facts")))
    assertEquals(db.stats.computedBy("parse"), 1)
    assertEquals(db.stats.computedBy("compile"), 1)
  }

  test("diagnostics come from the query, with positions in the file") {
    given db: Database = Database()
    db.set(SourceText, "bad.hgn", "p : int -> rel.\np X :- q X.\n")
    val diags = Ide.diagnostics(CompileKey("bad.hgn"))
    assertEquals(diags.flatMap(_.code), List("E0101"))
    assertEquals(diags.head.primarySpan.startLine, 1)
  }

  test("hover describes symbols and object variables") {
    given db: Database = setup()
    assertEquals(Ide.hover(key, at("roads =")), Some("meta definition roads : { path : ⇑(city -> city -> rel) }"))
    assertEquals(Ide.hover(key, at("graph)")), Some("signature graph = { node : type, edge : ⇑(node -> node -> rel) }"))
    assertEquals(Ide.hover(key, at("road :")), Some("relation road : city -> city -> rel"))
    assertEquals(Ide.hover(key, at("X Y :-")), Some("variable X : city"))
  }

  test("go to definition follows module paths into functor bodies and signatures") {
    given db: Database = setup()
    // `roads.path` in the %output directive → the `path` declared in the body of `tc`
    val d = Ide.definition(key, at("roads.path") + "roads.".length).get
    assertEquals(d.start, at("path :"))
    // `g.edge` → the field `edge` of the signature `graph`
    assertEquals(Ide.definition(key, at("g.edge") + 2).map(_.start), Some(at("edge :")))
    // `g` → the parameter of `tc`
    assertEquals(Ide.definition(key, at("g.edge")).map(_.start), Some(at("g : graph")))
  }

  test("references list the declaration and every use") {
    given db: Database = setup()
    val refs = Ide.references(key, at("road :"))
    assertEquals(refs.map(_.start), List(at("road :"), at("road."), at("road }")))
  }

  test("symbols give an outline with enclosing definitions") {
    given db: Database = setup()
    val outline = Ide.symbols(key).map(s => (s.name, s.container))
    assert(outline.contains(("path", Some("tc"))))
    assert(outline.contains(("roads", None)))
    assertEquals(outline.head, ("graph", None))
  }

  test("singleton variables are warned about (W0002), except names starting with `_`") {
    given db: Database = Database()
    db.set(SourceText, "s.hgn", "e : int -> int -> rel.\n%input e.\nsrc : int -> rel.\nsrc X :- e X Y, e X _Z.\n")
    val diags = Ide.diagnostics(CompileKey("s.hgn"))
    assertEquals(diags.map(d => (d.code, d.primarySpan.text)), List((Some("W0002"), "Y")))
  }
