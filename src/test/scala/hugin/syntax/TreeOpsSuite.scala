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

  /** The recursive definition `nodes` had before it walked an explicit stack (issue #60). */
  private def recursiveNodes(x: Any): Iterator[Any] =
    val children = x match
      case p: Product => p.productIterator.flatMap(recursiveNodes)
      case it: Iterable[?] => it.iterator.flatMap(recursiveNodes)
      case _ => Iterator.empty
    Iterator.single(x) ++ children

  test("nodes visits the nodes of the recursive definition, in its order, on the prelude and the golden programs") {
    import scala.jdk.CollectionConverters.*
    val dirs = List("run", "neg", "pos").map(d => java.nio.file.Path.of("tests", d)).filter(java.nio.file.Files.isDirectory(_))
    val files = dirs.flatMap(d => java.nio.file.Files.list(d).iterator.asScala.filter(_.toString.endsWith(".hgn")))
    val texts = hugin.compiler.SourceLoader.stdlib(hugin.compiler.SourceLoader.PreludePath).get :: files.map(java.nio.file.Files.readString)
    for text <- texts do
      val items = Parser.parse(SourceFile.virtual("t", text), Reporter()).items
      val expected = recursiveNodes(items).toVector
      val actual = TreeOps.nodes(items).toVector
      assertEquals(actual.length, expected.length)
      assert(actual.zip(expected).forall(_ == _), text.take(80))
  }
