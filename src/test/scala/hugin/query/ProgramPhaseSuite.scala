package hugin.query

import hugin.compiler.Settings
import hugin.util.*

/** The proof phase of a file (#186 P9f; reference: meta/index, "Order of elaboration"): its declarations
 *  about its own program (`here ⊢ r t̄`) are elaborated after its object items, by a query of their own
 *  cut off on the program's data. Editing a proof elaborates neither the declarations nor the object
 *  items; editing a rule elaborates that rule and the proofs, since the program changed; moving a rule
 *  elaborates nothing. The results equal those of a compilation from scratch. */
class ProgramPhaseSuite extends munit.FunSuite:
  private val settings = Settings(printAfter = Set("lower"))
  private val path = "phase.hgn"

  private val program =
    """%use "std/semantics".
      |city : type. berlin, paris, rome : city.
      |road : city -> city -> rel.
      |road berlin paris.
      |road paris rome.
      |path : city -> city -> rel.
      |path X Y :- road X Y.
      |path X Z :- road X Y, path Y Z.
      |limit : int = 3.
      |far : city -> rel.
      |far X :- path berlin X, limit > 2.
      |trans : {D : db} -> {x y z : ⇑city} -> here ⊢[D] path x y -> here ⊢[D] path y z -> here ⊢[D] path x z.
      |trans (path.1 R) Q = path.2 R Q.
      |trans (path.2 R P) Q = path.2 R (trans P Q).
      |%opaque trans.
      |""".stripMargin

  private def compile(using db: Database): Compiled = db(Compile, CompileKey(path, settings))

  private def edit(from: String, to: String)(using db: Database): Compiled =
    val text = db.get(SourceText, path)
    assert(text.contains(from), s"`$from` not in the program")
    db.set(SourceText, path, text.replace(from, to))
    db.stats.reset()
    compile

  private def counts(using db: Database): (Int, Int, Int) =
    (db.stats.computedBy("signatures"), db.stats.computedBy("elabItem"), db.stats.computedBy("elabDeferred"))

  private def rendered(c: Compiled): (List[String], List[String]) =
    val renderer = DiagnosticRenderer(color = false)
    (c.diagnostics.map(renderer.render), c.printed)

  test("proofs about the file's program: editing a proof, a rule, or moving a rule") {
    given db: Database = Database()
    db.set(SourceText, path, program)
    val first = compile
    assert(!first.hasErrors, first.diagnostics)
    assertEquals(counts._3, 1)
    // a proof: neither the declarations nor the object items are elaborated again
    val proof = edit("trans (path.1 R) Q = path.2 R Q.", "trans (path.1 E) Q = path.2 E Q.")
    assert(!proof.hasErrors, proof.diagnostics)
    assertEquals(counts, (0, 0, 1))
    // a comment before a rule, and a moved rule: the program is the same, nothing is elaborated
    edit("path X Y :- road X Y.", "(* the base case *)\npath X Y :- road X Y.")
    assertEquals(counts, (0, 0, 0))
    // a rule that the proofs do not mention changes the program: the proofs are elaborated again
    edit("far X :- path berlin X, limit > 2.", "far X :- path paris X, limit > 2.")
    assertEquals(counts, (0, 1, 1))
    // a rule the proof is about: the proof no longer fits, as from scratch
    val broken = edit("path X Z :- road X Y, path Y Z.", "path X Z :- path X Y, road Y Z.")
    assertEquals(counts, (0, 1, 1))
    assert(broken.hasErrors)
    val text = db.get(SourceText, path)
    val scratch = Database()
    scratch.set(SourceText, path, text)
    assertEquals(rendered(broken), rendered(scratch(Compile, CompileKey(path, settings))))
  }
