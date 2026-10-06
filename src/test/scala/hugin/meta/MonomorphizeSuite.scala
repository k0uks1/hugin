package hugin.meta

import hugin.TestSupport
import hugin.compiler.Context
import hugin.obj.*

/** Family instantiation (Section 4.6): inferred instances, rule families, polymorphic recursion, and a
 *  generic program that is left as it was. */
class MonomorphizeSuite extends munit.FunSuite:
  private val program = """
    ints : list int -> rel.
    ints (cons 1 nil).
    n : list int -> int -> rel.
    n L K :- ints L, len L K.
    %output n.
  """

  private def rel(p: ObjProgram, name: String): RelSym = p.rels.find(_.name == name).get

  test("family uses are instantiated at the inferred type arguments, rule families with them") {
    val c = TestSupport.compile(program, hugin.compiler.Settings(stopAfter = Some("monomorphize")))
    val p = c.unit.prog.nn
    assert(p.rels.exists(_.name == "len[int]"), p.rels.map(_.name))
    assert(p.rels.exists(_.name == "cons[int]"), p.rels.map(_.name))
    assert(p.types.exists(_.name == "list[int]"), p.types.map(_.name))
    assertEquals(ObjPrinter.relDecl(rel(p, "ints")), "ints : list[int] -> rel.")
    assertEquals(TestSupport.run(program), Right(List("n (cons 1 nil) 1.")))
  }

  test("the generic program is not changed: monomorphic declarations are copied") {
    val c = TestSupport.compile(program)
    assert(!c.reporter.hasErrors)
    val generic = c.unit.generic.nn
    val prog = c.unit.prog.nn
    assertEquals(ObjPrinter.relDecl(rel(generic, "ints")), "ints : list int -> rel.")
    assert(rel(generic, "ints") ne rel(prog, "ints"))
    val genericRels = generic.rels.toSet
    assert(prog.rels.forall(r => !genericRels(r)), "the program shares relation symbols with the generic program")
    // monomorphizing the same generic program again gives the same program
    given Context = c
    val again = Monomorphizer(generic).run()
    val first = Monomorphizer(generic).run()
    assertEquals(ObjPrinter.program(again), ObjPrinter.program(first))
    assertEquals(ObjPrinter.relDecl(rel(generic, "ints")), "ints : list int -> rel.")
  }

  test("polymorphic recursion is rejected (Definition 4.2)") {
    val code = """
      box A : type.
      put : A -> box A.
      nest : A -> rel.
      nest X :- start X.
      nest X :- nest (put X).
      start : int -> rel.
      start 1.
      ?- nest 1.
    """
    assertEquals(TestSupport.run(code).left.toOption.map(_.contains("E0205")), Some(true))
  }

  test("a type argument that is not determined is reported with an ascription (E0206)") {
    val c = TestSupport.compile("""
      e : rel.
      e :- len nil 0.
    """)
    val d = c.reporter.diagnostics.find(_.code.contains("E0206"))
    assert(d.exists(_.helps.exists(_.contains("ascribe"))), c.reporter.diagnostics)
  }
