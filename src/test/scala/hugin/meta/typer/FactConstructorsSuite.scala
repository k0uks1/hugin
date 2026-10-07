package hugin.meta.typer

import hugin.TestSupport
import hugin.meta.MType
import hugin.obj.*
import hugin.syntax.{Parser, Printer}
import hugin.util.{Reporter, SourceFile}

/** Data constructors (the default) and fact constructors (`%fact`): their meta types, subtyping, E0406 and
 *  the flag through monomorphization (docs/NOTES.md, "Data and fact constructors"). */
class FactConstructorsSuite extends munit.FunSuite:
  private lazy val typer = Typer(TestSupport.compile("t : type."))
  private val ints = List(Column(None, OType.Int))
  private val intInt = List(Column(None, OType.Int), Column(None, OType.Int))

  private def codes(code: String): List[String] = TestSupport.errorCodes(TestSupport.compile(code))

  test("a fact constructor is a data constructor, and a data constructor is not a relation") {
    assertEquals(typer.subsumes(MType.RelT(ints, Some(OType.Int)), MType.CtorT(ints, OType.Int)), None)
    assertEquals(typer.subsumes(MType.CtorT(ints, OType.Int), MType.CtorT(ints, OType.Int)), None)
    assert(typer.subsumes(MType.CtorT(ints, OType.Int), MType.RelT(ints, Some(OType.Int))).exists(_.contains("%fact")))
    assert(typer.subsumes(MType.CtorT(ints, OType.Int), MType.RelT(ints)).isDefined)
    assert(typer.subsumes(MType.RelT(ints), MType.CtorT(ints, OType.Int)).isDefined)
    assert(typer.subsumes(MType.CtorT(ints, OType.Int), MType.CtorT(intInt, OType.Int)).exists(_.contains("columns")))
  }

  test("data and fact constructors are shown apart") {
    assertEquals(typer.showMT(MType.CtorT(ints, OType.Int)), "⇑(int -> int)")
    assertEquals(typer.showMT(MType.RelT(ints, Some(OType.Int))), "%fact ⇑(int -> int)")
  }

  test("E0406: a data constructor read or derived as a relation") {
    val decls = "shape : type. circle : shape. square : int -> shape. has : shape -> rel. has circle. q : int -> rel.\n"
    assertEquals(codes(decls + "q N :- square N."), List("E0406"))
    assertEquals(codes(decls + "q 1 :- has S, not square 2."), List("E0406"))
    assertEquals(codes(decls + "q C :- C = count { N | square N }."), List("E0406"))
    assertEquals(codes(decls + "?- square N."), List("E0406"))
    assertEquals(codes(decls + "square 3 :- has circle."), List("E0406"))
    assertEquals(codes(decls + "%output square."), List("E0406"))
    assertEquals(codes(decls + "?- cons X nil."), List("E0406"))
  }

  test("terms built with data constructors are allowed everywhere a term is") {
    assertEquals(
      codes("""
        shape : type. square : int -> shape.
        has : shape -> rel. has (square 2).
        q : int -> rel.
        q N :- has (square N).
        r : shape -> rel.
        r S :- has S, S <> square 3, S = square _.
        s : int -> rel.
        s T :- T = sum { N | has (square N) }.
        a : (s : shape) -> (n : int) -> rel.
        %mode a +s -n.
        a (square N) N.
        b : int -> rel.
        b N :- a (square 4) N.
      """),
      Nil
    )
  }

  test("a fact constructor and a fact struct can be read; `%fact` applies to constructors and structs only") {
    assertEquals(
      codes("""
        shape : type. %fact square : int -> shape.
        %fact pt : type = { x : int, y : int }.
        square 2. pt 1 2.
        q : int -> rel.
        q N :- square N.
        q X :- pt { x = X, .. }.
      """),
      Nil
    )
    assertEquals(codes("%fact r : int -> rel."), List("E0103"))
    assertEquals(codes("shape : type. q : int -> rel. q N :- p { x = N, .. }. p : type = { x : int }."), List("E0406"))
  }

  test("a `%fact` signature field requires a fact constructor; a data field also takes a fact constructor") {
    val lib = "shape : type. square : int -> shape. %fact mark : int -> shape. "
    assertEquals(
      codes(lib + "s : mod = { shape : type, %fact c : int -> shape }. f (m : s) = { }. x = f { shape = shape, c = mark }."),
      Nil
    )
    assertEquals(codes(lib + "s : mod = { shape : type, c : int -> shape }. f (m : s) = { }. x = f { shape = shape, c = mark }."), Nil)
    assertEquals(
      codes(lib + "s : mod = { shape : type, %fact c : int -> shape }. f (m : s) = { }. x = f { shape = shape, c = square }."),
      List("E0203")
    )
    // inside a functor, only a `%fact` field can be read
    assertEquals(codes(lib + "f (m : { t : type, c : int -> t }) = { q : int -> rel. q N :- m.c N. }."), List("E0406"))
    assertEquals(codes(lib + "f (m : { t : type, %fact c : int -> t }) = { q : int -> rel. q N :- m.c N. }."), Nil)
    assertEquals(codes("f (m : { t : type, %fact n : t }) = { }."), List("E0004"))
  }

  test("a data constructor passed where a relation is expected is E0406") {
    assertEquals(
      codes("""
        shape : type. square : int -> shape.
        f (r : int -> rel) = { q : int -> rel. q N :- r N. }.
        x = f square.
      """),
      List("E0406")
    )
  }

  test("`%fact` is kept by monomorphization (every instance) and printed") {
    val c = TestSupport.compile("""
      tree A : type.
      leaf : A -> tree A.
      %fact node : tree A -> tree A -> tree A.
      t : tree int -> rel.
      t (node (leaf 1) (leaf 2)).
      l : tree int -> rel.
      l L :- node L _.
      %output l.
    """)
    assertEquals(TestSupport.errorCodes(c), Nil)
    val p = c.unit.prog.nn
    val node = p.rels.find(_.name == "node[int]").get
    val leaf = p.rels.find(_.name == "leaf[int]").get
    assert(node.fact && !node.isData)
    assert(!leaf.fact && leaf.isData)
    assert(ObjPrinter.relDecl(node).startsWith("%fact node[int] :"), ObjPrinter.relDecl(node))
  }

  test("the parser reads `%fact` on declarations and signature fields, and the printer writes it back") {
    val src = "%fact c : int -> t.\ns : mod = { t : type, %fact c : int -> t, d : int -> t }."
    val reporter = Reporter()
    val prog = Parser(SourceFile.virtual("p.hgn", src), reporter).parseProgram()
    assert(!reporter.hasErrors, reporter.diagnostics)
    // (the printer parenthesizes arrows)
    assertEquals(Printer.showProgram(prog), "%fact c : (int -> t).\ns : mod = { t : type, %fact c : (int -> t), d : (int -> t) }.")
  }
