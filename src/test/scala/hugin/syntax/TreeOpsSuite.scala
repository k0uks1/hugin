package hugin.syntax

import hugin.util.*

class TreeOpsSuite extends munit.FunSuite:
  private def decl(s: String): Trees.Decl =
    val r = Reporter()
    val p = Parser.parse(SourceFile.virtual("t", s), r)
    assert(!r.hasErrors, r.diagnostics.map(_.message).mkString("; "))
    p.items.head.asInstanceOf[Trees.Decl]

  test("flattenArrow: labelled domains and the codomain, through parentheses around arrows") {
    val (doms, cod) = TreeOps.flattenArrow(decl("c : (n : string) -> (int -> (list int -> rel)).").tpe)
    assertEquals(doms.map((l, d) => (l.map(_.name), Printer.show(d))), List((Some("n"), "string"), (None, "int"), (None, "list int")))
    assertEquals(TreeOps.flattenArrow(decl("c : (int -> int) -> rel.").tpe)._1.length, 1)
    assertEquals(Printer.show(cod), "rel")
    assertEquals(Printer.show(TreeOps.codomain(decl("c : int -> (rel).").tpe)), "rel")
  }

  test("flattenApp and headName: the head and arguments of an application") {
    val t = decl("c : (pair int (list int)).").tpe
    val (head, args) = TreeOps.flattenApp(t)
    assertEquals(Printer.show(head), "pair")
    assertEquals(args.map(Printer.show), List("int", "(list int)"))
    assertEquals(TreeOps.headName(decl("c : pair int int.").tpe).map(_.name), Some("pair"))
  }

  test("nodes enumerates a tree in preorder") {
    val vars = TreeOps.nodes(decl("c : f X (g Y) Z.").tpe).collect { case v: Trees.VarRef => v.name }.toList
    assertEquals(vars, List("X", "Y", "Z"))
  }
