package hugin.core

import hugin.cli.Main
import hugin.compiler.{Parsed, StdlibCache}
import hugin.core.elab.{Clauses, FreshNames}
import hugin.util.SourceFile
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** Differential test of the decisions without index unification in the split records of clause
 *  compilation (issue #60): with `Clauses.crossCheck`, every constructor decided to apply (its result is
 *  linear, or the scrutinee's indices are distinct free variables) is also unified, and a conflict is
 *  collected. Run on the bundled library and every program of the golden tests and examples. */
class ConstructorFastPathSuite extends munit.FunSuite:
  private def programs: List[Path] =
    (List("run", "neg", "pos", "recovery", "fix", "json").map(d => Path.of("tests", d)) :+ Path.of("examples"))
      .filter(Files.isDirectory(_))
      .flatMap(d => Files.list(d).iterator.asScala.filter(_.toString.endsWith(".hgn")).toList)
      .sortBy(_.toString)

  private def crossChecked[A](f: => A): (A, Long) =
    Clauses.crossCheck = true
    val before = Clauses.decidedWithoutUnifying.get
    Clauses.mismatches.clear()
    try
      val a = f
      assertEquals(Clauses.mismatches.asScala.toList, Nil, "constructors decided to apply that unification rules out")
      (a, Clauses.decidedWithoutUnifying.get - before)
    finally Clauses.crossCheck = false

  test("the bundled library: constructors decided without unification agree with it") {
    def items(p: Parsed) = SourceItems(p.source.path, "", Parsed(SourceFile.virtual(p.source.path, p.source.content)).program.items)
    val chain = StdlibCache.bundledChain()
    val (_, hits) = crossChecked(ProgramElab.preludeChain(chain.init.map(items), items(chain.last), builtinNames = true))
    assert(hits > 0, "no constructor was decided without unification")
  }

  test("golden programs and examples: constructors decided without unification agree with it") {
    val (_, hits) = crossChecked(programs.foreach(p => Main.run(List("check", p.toString, "--no-color"), _ => (), _ => ())))
    assert(hits > 0, "no constructor was decided without unification")
  }

  test("indexed and non-linear constructor results, and indices that are not distinct variables, are unified") {
    val src =
      """nat : Type.
        |zero : nat.
        |suc : nat -> nat.
        |vec : Type -> nat -> Type.
        |vnil : {A : Type} -> vec A zero.
        |vcons : {A : Type} -> {n : nat} -> A -> vec A n -> vec A (suc n).
        |vhead : {A : Type} -> {n : nat} -> vec A (suc n) -> A.
        |vhead (vcons X _) = X.
        |vlen : {A : Type} -> {n : nat} -> vec A (suc n) -> int.
        |vlen V = 1.
        |fin : nat -> Type.
        |fz : {n : nat} -> fin (suc n).
        |fs : {n : nat} -> fin n -> fin (suc n).
        |h : nat -> fin zero -> int.
        |h zero _ = 1.
        |same : Type -> Type -> Type.
        |srefl : {A : Type} -> same A A.
        |use : same int int -> int.
        |use srefl = 1.
        |both : {A : Type} -> same A A -> int.
        |both S = 1.
        |p : int -> rel.
        |""".stripMargin
    val f = Files.createTempFile("hugin-fastpath", ".hgn")
    Files.writeString(f, src)
    val err = StringBuilder()
    val (code, _) = crossChecked(Main.run(List("check", f.toString, "--no-color"), _ => (), s => err ++= s += '\n'))
    assertEquals(code, 0, err.toString)
  }

  test("fresh names of split records: the same names as a search from 1 every time") {
    // the definition the resumed search replaces
    final class Naive(taken0: Iterable[String]):
      private val taken = scala.collection.mutable.Set.from(taken0)
      def apply(base: String): String =
        val name = Iterator.from(1).map(k => if k == 1 && !taken(base) then base else s"$base$k").find(!taken(_)).get
        taken += name
        name
    val rnd = scala.util.Random(60)
    val bases = Vector("X", "X1", "X2", "Xs", "N", "N1", "T", "T2", "A")
    for _ <- 0 until 2000 do
      val taken =
        Vector.fill(rnd.nextInt(5))(bases(rnd.nextInt(bases.length)) + (if rnd.nextBoolean() then "" else rnd.nextInt(4).toString))
      val fresh = FreshNames(taken)
      val naive = Naive(taken)
      for _ <- 0 until rnd.nextInt(40) do
        val b = bases(rnd.nextInt(bases.length))
        assertEquals(fresh(b), naive(b), s"taken $taken")
  }
