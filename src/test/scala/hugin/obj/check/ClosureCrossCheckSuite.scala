package hugin.obj
package check

import hugin.TestSupport
import hugin.compiler.Context
import hugin.fuzz.{Corpus, Fuzz, ProgramGen}
import hugin.reference.CodeBlocks
import org.scalacheck.Gen
import org.scalacheck.rng.Seed

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** The antichain closure of [[SizeChange.check]] (issue #65) decides every recursive component as the
 *  full closure of [[FullClosure]] did wherever that finished under its old cap of 4000 graphs: on the
 *  goldens and examples, the worked examples of the design notes, the reference, the bench programs, and
 *  programs generated at a fixed seed. */
class ClosureCrossCheckSuite extends munit.FunSuite:
  /** Disagreements and the number of components compared. */
  private def compare(c: Context, origin: String): (List[String], Int) =
    if c.unit.prog == null then (Nil, 0)
    else
      val rs = Termination.recursive(c.unit).flatMap { rc =>
        val base = SizeChange.steps(rc.comp, rc.rules)
        FullClosure.check(base).map { (old, _) =>
          val now = SizeChange.check(rc.comp, rc.rules).isRight
          val (kept, failing) = SizeChange.closure(base)
          val keptFails = kept.exists(c => c.from == c.to && !c.graph.descendsLocally(c.from.arity))
          assertEquals((failing.isEmpty, keptFails), (now, !now), s"$origin: the antichain and the early stop disagree")
          Option.when(now != old)(s"$origin: ${rc.comp.mkString(", ")}: full closure says $old, antichain $now")
        }
      }
      (rs.flatten, rs.length)

  /** Compiles and compares on a thread with the launcher's stack (`-Xss64m`): the meta evaluator recurses
   *  on the structure it reduces, and nat literals (issue #131) make that structure deep. */
  private def all(programs: Iterator[(String, () => Context)]): (List[String], Int) =
    var result: Either[Throwable, (List[String], Int)] = Left(IllegalStateException("not run"))
    val body: Runnable = () =>
      result =
        try Right(programs.map((o, c) => compare(c(), o)).foldLeft((List.empty[String], 0))((a, b) => (a._1 ++ b._1, a._2 + b._2)))
        catch case e: Throwable => Left(e)
    val thread = Thread(null, body, "closure-cross-check", 64L << 20)
    thread.start()
    thread.join()
    result.fold(e => throw e, identity)

  private def hgn(root: String): List[Path] =
    Files.walk(Path.of(root)).iterator.asScala.filter(_.toString.endsWith(".hgn")).toList.sorted

  test("goldens, examples, design notes, bench programs and the reference") {
    val corpus = Corpus.entries.iterator.map(e => e.path -> (() => Fuzz.compile(e.program)))
    val files =
      // bench/meta/nat_literals.hgn has no recursive component and only stresses the elaboration of
      // large numerals (issue #131), which needs the launcher's stack; it is measured by the bench harness
      (hgn("docs/design/examples") ++ hgn("bench").filterNot(_.endsWith("nat_literals.hgn"))).iterator
        .map(p => p.toString -> (() => TestSupport.compile(Files.readString(p))))
    val reference =
      for
        page <- Files.walk(Path.of("reference/src")).iterator.asScala.filter(_.toString.endsWith(".md"))
        e <- CodeBlocks.examples(Files.readString(page)).getOrElse(Nil)
      yield s"$page:${e.line}" -> (() => TestSupport.compile(e.program))
    val (bad, n) = all(corpus ++ files ++ reference)
    assert(bad.isEmpty, bad.mkString("\n"))
    assert(n > 300, s"only $n components compared")
  }

  private def sample[A](gen: Gen[A], count: Int, seed: Long): Iterator[A] =
    Iterator.iterate(Seed(seed))(_.next).take(count).map(s => gen.pureApply(Gen.Parameters.default, s))

  test("generated programs at a fixed seed") {
    val generated =
      sample(ProgramGen.programs, 150, 20261010L).zipWithIndex.map((g, i) => s"generated #$i" -> (() => Fuzz.compile(g.program)))
    val integer =
      sample(SizeChangePrograms.program(), 300, 20261011L) ++ sample(SizeChangePrograms.program(8, three = true), 300, 20261012L)
    val recursion = integer.zipWithIndex.map((code, i) => s"integer recursion #$i:\n$code\n" -> (() => TestSupport.compile(code)))
    val (bad, n) = all(generated ++ recursion)
    assert(bad.isEmpty, bad.mkString("\n"))
    assert(n > 600, s"only $n components compared")
  }

  test("a component that exceeded the old cap is decided, with a handful of graphs") {
    val c = TestSupport.compile(Files.readString(Path.of("tests/run/t_termination_large_closure.hgn")))
    val List(rc) = Termination.recursive(c.unit): @unchecked
    val base = SizeChange.steps(rc.comp, rc.rules)
    assertEquals(FullClosure.check(base), None)
    assert(SizeChange.check(rc.comp, rc.rules).isRight)
    assert(SizeChange.closure(base)._1.length <= 3)
    assertEquals(FullClosure.check(base, cap = 20000).map(_._1), Some(true))
  }
