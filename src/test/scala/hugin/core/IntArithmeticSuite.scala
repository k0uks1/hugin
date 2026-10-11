package hugin.core

import hugin.TestSupport
import hugin.compiler.Settings
import hugin.core.elab.{Elaborator, FileEnv, NativeOperations}
import hugin.util.*

/** The meta `int` (issue #186 P4; reference: std/int): an inductive family with `ofNat` and `negSucc`
 *  whose closed values are numbers, and the native operations of `std/int`, which compute exactly as their
 *  clauses do (the method of `NatArithmeticSuite` for `std/nat`). */
class IntArithmeticSuite extends munit.FunSuite:
  private def resource(path: String): String =
    val in = getClass.getResourceAsStream(path)
    try new String(in.readAllBytes(), "UTF-8")
    finally in.close()

  private val intSource: String = resource("/hugin/stdlib/std/int.hgn")
  private val natSource: String = resource("/hugin/stdlib/std/nat.hgn")

  private val names = NativeOperations.intOperations.map(_._1)

  /** `std/int`'s functions, copied under the names `u<name>` into a program: the same clauses, but
   *  ordinary functions of the program, so they compute by their clauses (one constructor at a time, over
   *  the native operations of `std/nat`). */
  private val clauseCopies: String =
    val body = intSource.linesIterator.dropWhile(l => !l.startsWith("negOfNat :")).mkString("\n")
    names.foldLeft(body)((s, n) => s.replaceAll(s"\\b$n\\b", s"u$n"))

  private lazy val compiled: (Core, Map[String, Int]) =
    val code = s"%use \"std/nat\".\n%use \"std/int\".\n$clauseCopies\n"
    val c = TestSupport.compile(code, Settings(stopAfter = Some("elaborate")))
    assert(!c.reporter.hasErrors, c.reporter.diagnostics.map(_.message).mkString("\n"))
    val core = c.unit.elaborated.nn.core
    def find(n: String, path: String): Int =
      core.globals.indices.find(i => core.globals(i).name == n && core.globals(i).span.source.path == path).get
    val ids = names.flatMap(n => List(n -> find(n, NativeOperations.IntPath), s"u$n" -> find(s"u$n", "test.hgn"))).toMap
    (core, ids + ("nat" -> find("nat", NativeOperations.NatPath)))

  private def native(core: Core, id: Int): Option[NativeNat] = core.globals(id).kind match
    case GlobalKind.Function(_, Some(b)) => b.native
    case _ => None

  /** The operations whose arguments are natural numbers; the others take integers. */
  private val onNats = Set(NatOp.NegOfNat, NatOp.SubNatNat)

  /** The normal form of `f` applied to numbers: numerals of `nat` for `negOfNat` and `subNatNat`, meta
   *  integers otherwise. */
  private def call(f: String, args: BigInt*): Tm =
    val (core, ids) = compiled
    val op = NativeOperations.intOperations.find(o => o._1 == f || "u" + o._1 == f).get._2
    def arg(n: BigInt): Val = if onNats(op) then Val.Nat(ids("nat"), n) else Val.IntNum(n)
    val v = args.foldLeft(Val.Rigid(Head.Glob(ids(f)), Nil): Val)((acc, n) => core.app(acc, arg(n), Icit.Expl))
    core.quote(0, core.force(v))

  test("every operation of std/int is native, and the copies in a program are not") {
    val (core, ids) = compiled
    assertEquals(names.map(n => native(core, ids(n)).map(_.op)), NativeOperations.intOperations.map(o => Some(o._2)))
    assertEquals(names.map(n => native(core, ids(s"u$n"))), names.map(_ => None))
  }

  test("native and clause-defined evaluation agree (fixed seed)") {
    val rnd = scala.util.Random(186)
    for (n, op) <- NativeOperations.intOperations; _ <- 1 to 200 do
      val args = List.fill(op.arity)(if onNats(op) then BigInt(rnd.nextInt(41)) else BigInt(rnd.nextInt(81) - 40))
      assertEquals(call(n, args*), call(s"u$n", args*), s"$n ${args.mkString(" ")}")
    // the corners: zeros, ±1, equal arguments, division by zero and by negative numbers
    val corners = List(-2, -1, 0, 1, 2).map(BigInt(_))
    for (n, op) <- NativeOperations.intOperations; a <- corners; b <- corners do
      val args = List(a, b).take(op.arity).map(x => if onNats(op) then x.abs else x)
      assertEquals(call(n, args*), call(s"u$n", args*), s"$n ${args.mkString(" ")}")
    // around the 64-bit bounds, where `fits64` changes
    val bounds = List(BigInt(Long.MaxValue), BigInt(Long.MaxValue) + 1, BigInt(Long.MinValue), BigInt(Long.MinValue) - 1)
    for a <- bounds; n <- List("fits64", "ineg", "natAbs") do assertEquals(call(n, a), call(s"u$n", a), s"$n $a")
    for a <- bounds; b <- List(BigInt(-3), BigInt(7)); n <- List("iplus", "itimes", "idiv", "iless", "ileq", "iequal") do
      assertEquals(call(n, a, b), call(s"u$n", a, b), s"$n $a $b")
  }

  test("native operations compute on integers beyond 64 bits in one step") {
    val big = BigInt(10).pow(30)
    assertEquals(call("iplus", big, -big - 1), Tm.IntNum(-1))
    assertEquals(call("itimes", big, -big), Tm.IntNum(-big * big))
    assertEquals(call("idiv", -big, BigInt(7)), Tm.IntNum(-(big / 7)))
    assertEquals(call("idiv", big, BigInt(0)), Tm.IntNum(0))
    assertEquals(call("iminus", BigInt(Long.MinValue), BigInt(1)), Tm.IntNum(BigInt(Long.MinValue) - 1))
    val (_, ids) = compiled
    assertEquals(call("natAbs", -big), Tm.Nat(ids("nat"), big))
  }

  test("a closed integer is a number; its constructors are a view of it") {
    val (core, ids) = compiled
    val m = core.metaInt.nn
    def ctor(c: Int, n: Int): Tm = core.quote(0, core.force(core.app(Val.Rigid(Head.Glob(c), Nil), Val.Nat(ids("nat"), BigInt(n)), Icit.Expl)))
    assertEquals(ctor(m.ofNat, 5), Tm.IntNum(5))
    assertEquals(ctor(m.negSucc, 2), Tm.IntNum(-3))
    assertEquals(core.natView(Val.IntNum(-3)), Val.Rigid(Head.Glob(m.negSucc), List(Elim.EApp(Val.Nat(ids("nat"), BigInt(2)), Icit.Expl))))
    assertEquals(core.natView(Val.IntNum(0)), Val.Rigid(Head.Glob(m.ofNat), List(Elim.EApp(Val.Nat(ids("nat"), BigInt(0)), Icit.Expl))))
  }

  /** `std/nat` and `std/int` elaborated as the library files, with `edit` applied to `std/int`. */
  private def asLibraries(edit: String => String): Core =
    val reporter = Reporter()
    val core = Core()
    val nat = natSource.replace("%use \"std/reflect\" (bool, true, false).", "bool : Type. true : bool. false : bool.")
    val natProg = hugin.syntax.Parser.parse(SourceFile.virtual(NativeOperations.NatPath, nat), reporter)
    val natElab = Elaborator(core, reporter, FileEnv(path = NativeOperations.NatPath))
    natElab.elabProgram(natProg.items)
    assert(!reporter.hasErrors, reporter.diagnostics.map(_.message).mkString("\n"))
    val opened = List("bool", "true", "false", "nat", "zero", "suc", "int", "ofNat", "negSucc", "plus", "times", "divSucAux", "equal", "less")
    val parent = opened.map(n => n -> natElab.scope(n)).toMap
    val int = edit(intSource.replace("%use \"std/reflect\" (bool, true, false).\n%use \"std/nat\".", ""))
    val intProg = hugin.syntax.Parser.parse(SourceFile.virtual(NativeOperations.IntPath, int), reporter)
    Elaborator(core, reporter, FileEnv(path = NativeOperations.IntPath, parent = parent)).elabProgram(intProg.items)
    assert(!reporter.hasErrors, reporter.diagnostics.map(_.message).mkString("\n"))
    core

  test("the library's operations are checked against their equations") {
    val core = asLibraries(identity)
    val bound = core.globals.toList.flatMap(g =>
      g.kind match
        case GlobalKind.Function(_, Some(b)) => b.native.filterNot(n => NativeOperations.operations.exists(_._2 == n.op)).map(n => g.name -> n.op)
        case _ => None
    )
    assertEquals(bound, NativeOperations.intOperations)
  }

  test("a wrong clause in the library is an internal error") {
    val e = intercept[Exception](asLibraries(_.replace("iplus (negSucc M) (negSucc N) = negSucc (plus M N + 1).", "iplus (negSucc M) (negSucc N) = negSucc (plus M N).")))
    assert(e.getMessage.contains("`iplus` is not the native int add"), e.getMessage)
    val e2 = intercept[Exception](asLibraries(_.replace("idiv (ofNat M) (ofNat 0) = 0.", "idiv (ofNat M) (ofNat 0) = ofNat M.")))
    assert(e2.getMessage.contains("`idiv` is not the native int div"), e2.getMessage)
    val e3 = intercept[Exception](asLibraries(_.replace("fits64 (negSucc N) = less N 9223372036854775808.", "fits64 (negSucc N) = less N 9223372036854775807.")))
    assert(e3.getMessage.contains("`fits64` is not the native fits64"), e3.getMessage)
  }

  test("hover says that a function of std/int is native") {
    import hugin.query.*
    val program = "%use \"std/int\".\nx : int = itimes 2 3.\n"
    given db: Database = Database()
    db.set(SourceText, "p.hgn", program)
    val hover = Ide.hover(CompileKey("p.hgn"), program.indexOf("itimes")).getOrElse("")
    assert(hover.endsWith("\n(native: int mul)"), hover)
  }
