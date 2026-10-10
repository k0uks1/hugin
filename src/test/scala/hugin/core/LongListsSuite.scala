package hugin.core

import CoreTesting.*
import java.util.concurrent.FutureTask

/** Long lists through the meta level (issue #88): a long list is a deep value (`x1 :: (x2 :: …)`), and the
 *  bench harness's `meta_scaled` (a module-wide directive recursing over a module of ~190 items) overflowed
 *  the JVM's default 1 MiB stack. The compiler's own walks over list data (memo keys, evaluation of list
 *  data, the elements of a module) are loops, and a meta function's recursion is evaluated with an
 *  explicit continuation stack on the heap ([[Machine]], issue #129), so its depth costs no JVM stack.
 *  Each test runs on a thread with the JVM's default stack size (1 MiB, the main thread of
 *  `sbt "Test/runMain hugin.bench.Bench warm"`), not the launcher's 64 MiB. */
class LongListsSuite extends munit.FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(5, "min")

  import LongListsSuite.*

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

  private def mirrored(n: Int): Unit =
    val out = onDefaultStack(mirrorOutput(n)).fold(e => fail(s"errors: $e"), identity)
    assertEquals(out.count(_.matches("X = \\d+\\.")), n)
    assert(out.contains("X = n1, Y = n0."), out.mkString("\n").take(2000))

  test("a meta function recursing over a module of 400 items with a deep case tree (bench meta_scaled)") {
    mirrored(400)
  }

  test("a meta function recursing 5000 levels deep on a 1 MiB stack (explicit continuation stack, issue #129)") {
    // one level of the recursion per item: before #129 a few hundred levels overflowed 1 MiB, at a depth
    // that varied with the JIT
    mirrored(5000)
  }

  test("the 400 items on a 1 MiB stack in an interpreted JVM (-Xint: the largest frames, no JIT)") {
    // before #129 this overflowed on every run; with the JIT it overflowed about one run in five
    val javaBin = java.nio.file.Paths.get(sys.props("java.home"), "bin", "java").toString
    val cp = sys.props("java.class.path")
    val p = ProcessBuilder(javaBin, "-Xint", "-cp", cp, "hugin.core.LongListsInterpreted").redirectErrorStream(true).start()
    val out = String(p.getInputStream.readAllBytes())
    assertEquals(p.waitFor(), 0, out.take(4000))
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

object LongListsSuite:
  /** `body` on a new thread with the JVM's default stack size, 1 MiB. */
  def onDefaultStack[A](body: => A): A =
    val task = FutureTask[A](() => body)
    val thread = Thread(null, task, "long-lists", 1L << 20)
    thread.start()
    try task.get()
    catch case e: java.util.concurrent.ExecutionException => throw e.getCause

  def items(n: Int): String = (1 to n).map(i => s"q $i.").mkString("\n")

  /** A meta function recursing over a module of `n` items, one level per item, with a deep case tree:
   *  `mirror`'s first clause splits a dozen times per item (before #88, every split cost three frames). */
  def mirrorOutput(n: Int): Either[List[String], List[String]] =
    hugin.TestSupport.run(
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
         |${items(n)}
         |%mirror.
         |?- q X.
         |?- edge X Y.
         |""".stripMargin
    )

/** `mirrorOutput(n)` (400 by default) on a 1 MiB stack, for a JVM run with `-Xint` by [[LongListsSuite]]: exit code 0 if
 *  it gives the `n` answers and the mirrored edge. */
object LongListsInterpreted:
  def main(args: Array[String]): Unit =
    val n = args.headOption.fold(400)(_.toInt)
    val ok =
      try
        LongListsSuite.onDefaultStack(LongListsSuite.mirrorOutput(n)) match
          case Right(out) =>
            val good = out.count(_.matches("X = \\d+\\.")) == n && out.contains("X = n1, Y = n0.")
            if !good then println(out.mkString("\n").take(2000))
            good
          case Left(errors) => println(s"errors: $errors"); false
      catch
        case e: StackOverflowError => println(s"StackOverflowError (${e.getStackTrace.length} frames)"); false
    Console.flush()
    System.exit(if ok then 0 else 1)
