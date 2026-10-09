package hugin.core

import CoreTesting.*
import java.util.concurrent.FutureTask

/** Long lists through the meta level (issue #88): a long list is a deep value (`x1 :: (x2 :: …)`), and the
 *  bench harness's `meta_scaled` (a module-wide directive recursing over a module of ~190 items) overflowed
 *  the JVM's default 1 MiB stack. The compiler's own walks over list data (memo keys, evaluation of list
 *  data, the elements of a module) are loops, and the JVM stack a meta function's recursion uses per level
 *  does not grow with the depth of its case tree. Each test runs on a thread with the JVM's default stack
 *  size (1 MiB, the main thread of `sbt "Test/runMain hugin.bench.Bench warm"`), not the launcher's 64 MiB. */
class LongListsSuite extends munit.FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(5, "min")

  private def onDefaultStack[A](body: => A): A =
    val task = FutureTask[A](() => body)
    val thread = Thread(null, task, "long-lists", 1L << 20)
    thread.start()
    try task.get()
    catch case e: java.util.concurrent.ExecutionException => throw e.getCause

  private def items(n: Int): String = (1 to n).map(i => s"q $i.").mkString("\n")

  private def outputCount(code: String): Int =
    hugin.TestSupport.run(code) match
      case Right(out) => out.count(_.matches("X = \\d+\\."))
      case Left(errors) => fail(s"errors: $errors")

  test("a module-wide directive over a module of 5000 items (memo keys, list data, elements)") {
    val code =
      s"""%use "std/reflect".
         |q : int -> rel.
         |keep : module -> module.
         |keep M = M.
         |swap : module -> module.
         |swap (A :: B :: R) = B :: A :: R.
         |swap M = M.
         |${items(5000)}
         |%keep.
         |%swap.
         |?- q X.
         |""".stripMargin
    assertEquals(onDefaultStack(outputCount(code)), 5000)
  }

  test("a meta function recursing over a module of 400 items with a deep case tree (bench meta_scaled)") {
    // `mirror`'s first clause splits a dozen times per item: before #88, every split cost three frames
    val code =
      s"""%use "std/reflect".
         |node : type.
         |edge : node -> node -> rel.
         |n0 : node. n1 : node.
         |edge n0 n1.
         |q : int -> rel.
         |mirror : module -> module.
         |mirror [] = [].
         |mirror ('( edge $$X $$Y :- $$..B ) :: Rest) = '( edge $$X $$Y :- $$..B ) :: '( edge $$Y $$X :- $$..B ) :: mirror Rest.
         |mirror (I :: Rest) = I :: mirror Rest.
         |${items(400)}
         |%mirror.
         |?- q X.
         |?- edge X Y.
         |""".stripMargin
    val out = onDefaultStack(hugin.TestSupport.run(code)).fold(e => fail(s"errors: $e"), identity)
    assertEquals(out.count(_.matches("X = \\d+\\.")), 400)
    assert(out.contains("X = n1, Y = n0."), out.mkString("\n").take(2000))
  }

  test("memo keys and evaluation of a list of 100 000 elements") {
    val e = ok(
      """nat : Type.
        |zero : nat.
        |suc : nat -> nat.
        |vlist : Type.
        |vnil : vlist.
        |vcons : nat -> vlist -> vlist.
        |""".stripMargin
    )
    val core = e.core
    val Seq(zero, suc, vnil, vcons) = Seq("zero", "suc", "vnil", "vcons").map(e.elab.scope(_))
    def tm(n: Int): Tm = (0 until n).foldLeft(Tm.Global(vnil): Tm) { (acc, i) =>
      val x = if i % 2 == 0 then Tm.Global(zero) else Tm.App(Tm.Global(suc), Tm.Global(zero), Icit.Expl)
      Tm.App(Tm.App(Tm.Global(vcons), x, Icit.Expl), acc, Icit.Expl)
    }
    onDefaultStack {
      val (a, b, c) = (core.eval(Nil, tm(100000)), core.eval(Nil, tm(100000)), core.eval(Nil, tm(99999)))
      val ka = core.closedKeyIds(List(a))
      assert(ka.isDefined)
      assertEquals(core.closedKeyIds(List(a)), ka)
      assertEquals(core.closedKeyIds(List(b)), ka)
      assertNotEquals(core.closedKeyIds(List(c)), ka)
    }
  }
