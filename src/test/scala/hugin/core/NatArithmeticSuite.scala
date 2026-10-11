package hugin.core

import hugin.TestSupport
import hugin.compiler.Settings
import hugin.core.elab.{Elaborator, FileEnv, NativeOperations}
import hugin.util.*

/** Native arithmetic of `std/nat` (issue #131 batch 3; reference: std/nat, native arithmetic): the
 *  operations compute on numbers exactly as their clauses do, they are bound only to `std/nat`'s
 *  functions, and a library whose clauses do not define the operation is an internal error. */
class NatArithmeticSuite extends munit.FunSuite:
  private val natSource: String =
    val in = getClass.getResourceAsStream("/hugin/stdlib/std/nat.hgn")
    try new String(in.readAllBytes(), "UTF-8")
    finally in.close()

  private val names = NativeOperations.operations.map(_._1)

  /** `std/nat`'s functions, copied under the names `u<name>` into a program: the same clauses, but
   *  ordinary functions of the program, so they compute by their clauses (one constructor at a time). */
  private val unaryCopies: String =
    val body = natSource.linesIterator
      .dropWhile(l => !l.startsWith("plus :"))
      .mkString("\n")
    names.foldLeft(body)((s, n) => s.replaceAll(s"\\b$n\\b", s"u$n"))

  private lazy val compiled: (Core, Map[String, Int]) =
    val code = s"%use \"std/nat\".\n$unaryCopies\n"
    val c = TestSupport.compile(code, Settings(stopAfter = Some("elaborate")))
    assert(!c.reporter.hasErrors, c.reporter.diagnostics.map(_.message).mkString("\n"))
    val core = c.unit.elaborated.nn.core
    def find(n: String, path: String): Int =
      core.globals.indices.find(i => core.globals(i).name == n && core.globals(i).span.source.path == path).get
    val ids = names.flatMap(n => List(n -> find(n, NativeOperations.NatPath), s"u$n" -> find(s"u$n", "test.hgn"))).toMap
    (core, ids + ("nat" -> find("nat", NativeOperations.NatPath)))

  private def native(core: Core, id: Int): Option[NativeNat] = core.globals(id).kind match
    case GlobalKind.Function(_, Some(b)) => b.native
    case _ => None

  /** The normal form of `f` applied to numerals. */
  private def call(f: String, args: BigInt*): Tm =
    val (core, ids) = compiled
    val v = args.foldLeft(Val.Rigid(Head.Glob(ids(f)), Nil): Val)((acc, n) => core.app(acc, Val.Nat(ids("nat"), n), Icit.Expl))
    core.quote(0, core.force(v))

  test("every operation of std/nat is native, and the copies in a program are not") {
    val (core, ids) = compiled
    assertEquals(names.map(n => native(core, ids(n)).map(_.op)), NativeOperations.operations.map(o => Some(o._2)))
    assertEquals(names.map(n => native(core, ids(s"u$n"))), names.map(_ => None))
  }

  test("native and unary evaluation agree on small numerals (fixed seed)") {
    val rnd = scala.util.Random(131)
    def small(max: Int) = BigInt(rnd.nextInt(max + 1))
    for (n, op) <- NativeOperations.operations; _ <- 1 to 150 do
      val args = List.fill(op.arity)(small(if op.arity == 4 then 12 else 40))
      val (nat, unary) = (call(n, args*), call(s"u$n", args*))
      assertEquals(nat, unary, s"$n ${args.mkString(" ")}")
    // the corners: zeros, equal arguments, division by 1
    for (n, op) <- NativeOperations.operations; a <- 0 to 3; b <- 0 to 3 do
      val args = List(a, b, a, b).take(op.arity).map(BigInt(_))
      assertEquals(call(n, args*), call(s"u$n", args*), s"$n ${args.mkString(" ")}")
  }

  test("native operations compute on large numerals") {
    val (_, ids) = compiled
    val fam = ids("nat")
    assertEquals(call("times", BigInt(123456789), BigInt(987654321)), Tm.Nat(fam, BigInt("121932631112635269")))
    assertEquals(call("plus", BigInt(10).pow(30), BigInt(1)), Tm.Nat(fam, BigInt(10).pow(30) + 1))
    assertEquals(call("minus", BigInt(5), BigInt(10).pow(20)), Tm.Nat(fam, BigInt(0)))
    // 10^20 divided by 7 and its remainder: `divSucAux 0 6 n 6`
    assertEquals(call("divSucAux", 0, 6, BigInt(10).pow(20), 6), Tm.Nat(fam, BigInt(10).pow(20) / 7))
    assertEquals(call("modSucAux", 0, 6, BigInt(10).pow(20), 6), Tm.Nat(fam, BigInt(10).pow(20) % 7))
    assertEquals(call("toInt", BigInt(10).pow(12)), Tm.Lit(hugin.syntax.Literal.IntL(1000000000000L), Stage.S1))
  }

  test("toInt beyond the 64-bit meta int is stuck") {
    val (_, ids) = compiled
    val n = BigInt(Long.MaxValue) + 1
    assertEquals(call("toInt", n), Tm.App(Tm.Global(ids("toInt")), Tm.Nat(ids("nat"), n), Icit.Expl))
  }

  /** `std/nat`'s text elaborated as the library file, with `edit` applied (its own `bool`). */
  private def asLibrary(edit: String => String): Core =
    val text = edit(natSource.replace("%use \"std/reflect\" (bool, true, false).", "bool : Type. true : bool. false : bool."))
    val reporter = Reporter()
    val prog = hugin.syntax.Parser.parse(SourceFile.virtual(NativeOperations.NatPath, text), reporter)
    val core = Core()
    Elaborator(core, reporter, FileEnv(path = NativeOperations.NatPath)).elabProgram(prog.items)
    assert(!reporter.hasErrors, reporter.diagnostics.map(_.message).mkString("\n"))
    core

  test("the library's operations are checked against their equations") {
    val core = asLibrary(identity)
    val bound = core.globals.toList.flatMap(g =>
      g.kind match
        case GlobalKind.Function(_, Some(b)) => b.native.map(n => g.name -> n.op)
        case _ => None
    )
    assertEquals(bound, NativeOperations.operations)
  }

  test("a wrong equation in the library is an internal error") {
    val e = intercept[Exception](asLibrary(_.replace("plus N (M + 1) = plus N M + 1.", "plus N (M + 1) = plus N M + 2.")))
    assert(e.getMessage.contains("`plus` is not the native add"), e.getMessage)
    val e2 = intercept[Exception](asLibrary(_.replace("less N 0 = false.", "less N 0 = true.")))
    assert(e2.getMessage.contains("`less` is not the native lt"), e2.getMessage)
  }

  test("a program's own plus is clause-defined, also with the library's clauses") {
    val e = CoreTesting.ok(
      """nat : Type. zero : nat. suc : nat -> nat.
        |plus : nat -> nat -> nat.
        |plus N 0 = N.
        |plus N (M + 1) = plus N M + 1.
        |""".stripMargin
    )
    e.global("plus").kind match
      case GlobalKind.Function(_, Some(b)) => assertEquals(b.native, None)
      case k => fail(s"not a function: $k")
    assertEquals(e.eval("plus 2 3"), "5")
  }

  test("hover says that a function of std/nat is native") {
    import hugin.query.*
    val program = "%use \"std/nat\".\nx : nat = times 2 3.\ny : nat = plus x 1.\n"
    given db: Database = Database()
    db.set(SourceText, "p.hgn", program)
    val key = CompileKey("p.hgn")
    val times = Ide.hover(key, program.indexOf("times")).getOrElse("")
    assert(times.endsWith("\n(native: mul)"), times)
    assert(Ide.hover(key, program.indexOf("plus")).exists(_.endsWith("\n(native: add)")))
  }
