package hugin.query

import hugin.core.{ElaboratedDeclarations, ElaboratedItem, ProgramElab}
import hugin.util.{DiagnosticRenderer, Reporter}

/** Items elaborated against one declarations' core are moved onto another by the stable keys of the
 *  declarations' globals (`hugin.core.Rebase`, issue #126, PR 7 step 1): the program assembled from them
 *  is the program assembled from items elaborated against the new declarations, also when a declaration
 *  added before the others shifts every global id. */
class RebaseSuite extends munit.FunSuite:
  private val path = "rebase.hgn"
  private val program =
    """graph : Type = { node : type, edge : node -> node -> rel }.
      |tc (g : graph) = {
      |  path : g.node -> g.node -> rel.
      |  path X Y :- g.edge X Y.
      |  path X Z :- g.edge X Y, path Y Z.
      |}.
      |city : type. berlin : city. paris : city. rome : city.
      |road : city -> city -> rel.
      |road berlin paris. road paris rome.
      |roads = tc { node = city, edge = road }.
      |limit : int = 3.
      |small : int -> rel.
      |small N :- N = limit.
      |pair : list int -> rel.
      |pair (cons 1 (cons limit nil)).
      |?- roads.path berlin X.
      |?- small N.
      |""".stripMargin

  /** The declarations and object items of `text`, through the query database. */
  private def parts(text: String): (ElaboratedDeclarations, List[hugin.syntax.Trees.Item], List[hugin.syntax.Trees.Item], Database) =
    val db = Database()
    db.set(SourceText, path, text)
    val key = ProgramKey(path, true)
    (db(Signatures, key), db(DeclarationsOf, key).items, db(ObjectItemsOf, key).items.map(_._2), db)

  private def rendered(decls: ElaboratedDeclarations, items: List[ElaboratedItem]): (List[String], List[String]) =
    val (elaborated, diagnostics, _) = ProgramElab.assemble(decls, items)
    (elaborated.render(Reporter()), diagnostics.map(DiagnosticRenderer(color = false).render))

  test("items elaborated against equal declarations built again are moved, not elaborated again") {
    val (decls, declItems, objects, _) = parts(program)
    val again = ProgramElab.declarations(decls.base, path, List(path), declItems)
    assert(again.core ne decls.core)
    val old = objects.map(ProgramElab.item(decls, _))
    assertEquals(rendered(again, old), rendered(again, objects.map(ProgramElab.item(again, _))))
  }

  test("a declaration added before the others shifts every global; items not using it are moved by key") {
    val (decls, _, _, _) = parts(program)
    val (_, newDeclItems, newObjects, _) = parts("first : type. other : first.\n" + program)
    // the new declarations on the same libraries' core as the old ones (one database per text here)
    val newDecls = ProgramElab.declarations(decls.base, path, List(path), newDeclItems)
    assert(newDecls.core.globals.length > decls.core.globals.length)
    // the program's object items, elaborated against the old declarations (they do not use `first`)
    val moved = newObjects.map(ProgramElab.item(decls, _))
    assertEquals(rendered(newDecls, moved), rendered(newDecls, newObjects.map(ProgramElab.item(newDecls, _))))
  }

  test("an item that uses a declaration that is gone is elaborated again, as from scratch") {
    val (decls, _, objects, _) = parts(program)
    val (_, newDeclItems, _, _) = parts(program.replace("limit : int = 3.", "limit : int = 4."))
    val newDecls = ProgramElab.declarations(decls.base, path, List(path), newDeclItems)
    // `limit` keeps its key: moved by key (step 3 compares what the items read before reusing them)
    val moved = objects.map(ProgramElab.item(decls, _))
    assertEquals(rendered(newDecls, moved)._2, rendered(newDecls, objects.map(ProgramElab.item(newDecls, _)))._2)
    // a renamed declaration has no counterpart: the items using it are elaborated again
    val (_, renamedItems, _, _) = parts(program.replace("limit", "bound"))
    val renamed = ProgramElab.declarations(decls.base, path, List(path), renamedItems)
    val usesLimit = objects.filter(_.toString.contains("limit"))
    assert(usesLimit.nonEmpty)
    val (lines, diagnostics) = rendered(renamed, usesLimit.map(ProgramElab.item(decls, _)))
    assertEquals((lines, diagnostics), rendered(renamed, usesLimit.map(ProgramElab.item(renamed, _))))
  }

  test("renamed declarations of every kind: the items are moved or elaborated again, as from scratch") {
    // with an item that creates a family instance over a declaration (`list city`, in no declaration)
    val text = program + "via : rel.\nvia :- road X Y, Z = cons X (cons Y nil).\n"
    val (decls, _, objects, _) = parts(text)
    for (name, to) <- List("city" -> "town", "road" -> "street", "limit" -> "bound", "graph" -> "net") do
      val (_, newDeclItems, _, _) = parts(text.replace(name, to))
      val newDecls = ProgramElab.declarations(decls.base, path, List(path), newDeclItems)
      val old = objects.map(ProgramElab.item(decls, _))
      // the diagnostics as a sequence: assembly reports every item's in item order, moved or not
      assertEquals(rendered(newDecls, old), rendered(newDecls, objects.map(ProgramElab.item(newDecls, _))), name)
  }
