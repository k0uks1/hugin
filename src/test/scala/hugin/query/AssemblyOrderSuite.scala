package hugin.query

import hugin.core.ProgramElab
import hugin.util.DiagnosticRenderer

/** Assembly reports the diagnostics of the items in item order, whether an item is moved from its own
 *  elaboration or elaborated again in assembly (an item that is not portable, such as one instantiating
 *  a module): the order a user and an editor see does not depend on which items were reused. */
class AssemblyOrderSuite extends munit.FunSuite:
  private val path = "order.hgn"
  private val program =
    """graph : Type = { node : type, edge : node -> node -> rel }.
      |tc (g : graph) = {
      |  path : g.node -> g.node -> rel.
      |  path X Y :- g.edge X Y.
      |  path X Z :- g.edge X Y, path Y Z.
      |}.
      |city : type. berlin : city. paris : city.
      |road : city -> city -> rel.
      |road berlin paris.
      |early : rel.
      |early :- road A B.
      |t : rel.
      |t :- (tc { node = city, edge = road }).path berlin Z.
      |s : rel.
      |s :- road X Y.
      |""".stripMargin

  private def render(ds: List[hugin.util.Diagnostic]): List[String] = ds.map(DiagnosticRenderer(color = false).render)

  test("a mixed assembly reports each item's diagnostics in item order") {
    val db = Database()
    db.set(SourceText, path, program)
    val key = ProgramKey(path, true)
    val decls = db(Signatures, key)
    val items = db(ObjectItemsOf, key).items.map(_._2).map(ProgramElab.item(decls, _))
    // a mix: `t` instantiates a module and is elaborated again in assembly, the others are moved
    assertEquals(items.map(_.portable), List(true, true, false, true))
    assert(items.forall(_.item.span.exists))
    val (_, diagnostics, _) = ProgramElab.assemble(decls, items)
    val expected = decls.base.diagnostics ++ decls.diagnostics ++ items.flatMap(_.diagnostics)
    assertEquals(render(diagnostics), render(expected))
    val starts = diagnostics.map(_.primarySpan.start)
    assertEquals(starts, starts.sorted)
    assertEquals(starts.length, 5) // A, B in `early`; Z in `t`; X, Y in `s`
  }
