package hugin.meta

import hugin.TestSupport
import hugin.compiler.{Context, Settings}
import hugin.obj.{ObjPrinter, Term, Var}
import hugin.syntax.TreeOps

/** Meta evaluation (Section 4.5): module bodies with fresh prefixes, hygienic expansion of formula
 *  functions, cross-stage persistence, recorded signature requirements. */
class MetaEvalSuite extends munit.FunSuite:
  private def generic(code: String): (Context, String) =
    val c = TestSupport.compile(code, Settings(stopAfter = Some("metaEval")))
    assert(!c.reporter.hasErrors, c.reporter.diagnostics.map(_.message))
    (c, ObjPrinter.program(c.unit.generic.nn))

  test("each functor application has its own prefix") {
    val (_, out) = generic("""
      city : type.
      road : city -> city -> rel.
      rail : city -> city -> rel.
      roads = tc { node = city, edge = road }.
      rails = tc { node = city, edge = rail }.
    """)
    assert(out.contains("roads.path : city -> city -> rel."), out)
    assert(out.contains("rails.path : city -> city -> rel."), out)
    assert(out.contains("roads.path X Y :- road X Y."), out)
    assert(out.contains("rails.path X Z :- rail X Y, rails.path Y Z."), out)
  }

  test("formula functions expand hygienically: their local variables do not capture the caller's") {
    val (c, _) = generic("""
      e : int -> int -> rel.
      two : int -> prop.
      two X :- e X Y, e Y _.
      p : int -> int -> rel.
      p X Y :- two X, e X Y.
    """)
    val rule = c.unit.generic.nn.rules.find(_.heads.headOption.exists(h => ObjPrinter.term(h) == "p X Y")).get
    val vars = TreeOps.nodes(rule.body).collect { case v: Term.Var => v.name }.filterNot(Var.isWild).toList.distinct
    // the clause's variables are renamed apart (`Y#1` prints as `Y` but is not the rule's `Y`)
    assertEquals(vars.toSet, Set("X", "X#1", "Y#1", "Y"))
    assertEquals(vars.map(Var.display).toSet, Set("X", "Y"))
  }

  test("compile-time values used in object code are persisted as literals") {
    val (_, out) = generic("""
      k : int = 6 * 7.
      p : int -> rel.
      p X :- X = k.
    """)
    assert(out.contains("p X :- X = 42."), out)
  }

  test("a program's declaration shadowing the prelude's renames the prelude's object") {
    val (_, out) = generic("""
      len : int -> rel.
      len 1.
    """)
    assert(out.linesIterator.exists(_.startsWith("prelude.len [A] : ")), out)
    assert(out.linesIterator.contains("len : int -> rel."), out)
  }

  test("signature requirements are recorded and checked once directives are attached (E0208)") {
    val code = """
      city : type.
      road : city -> city -> rel.
      %open road.
      g : mod = { node : type, edge : node -> node -> rel, %complete edge }.
      reach (x : g) = { r : x.node -> rel. r N :- x.edge N _. }.
      a = reach { node = city, edge = road }.
    """
    val (c, _) = generic(code)
    assertEquals(c.unit.requirements.map(r => (r.requirement.label, r.rel.name)), List(("edge", "road")))
    assertEquals(TestSupport.errorCodes(TestSupport.compile(code)), List("E0208"))
  }
