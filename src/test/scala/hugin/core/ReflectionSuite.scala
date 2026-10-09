package hugin.core

import hugin.TestSupport
import hugin.compiler.Settings
import hugin.core.elab.{Cxt, RKind}
import hugin.obj.ObjPrinter
import hugin.syntax.{Parser, Printer}
import hugin.syntax.Trees.*
import hugin.util.*

/** Reflection (reference: reflection): the syntax of quotes and holes, round trips between object
 *  syntax and reflective data, quoted patterns (symbols, coverage, termination), higher-order holes. */
class ReflectionSuite extends munit.FunSuite:
  private def show(code: String): String =
    val r = Reporter()
    val items = Parser.parse(SourceFile.virtual("t.hgn", code), r).items
    assert(r.diagnostics.isEmpty, r.diagnostics.map(_.message).mkString("\n"))
    items.map(Printer.showItem).mkString("\n")

  test("syntax: lists, lambdas, quotes, holes") {
    assertEquals(show("x = [a, b]."), "x = [a, b].")
    assertEquals(show("x = f [] [a]."), "x = f [] [a].")
    assertEquals(show("x = [y] y."), "x = [y] y.")
    assertEquals(show("x = [Y]."), "x = [Y].")
    assertEquals(show("x = a :: b :: []."), "x = (a :: (b :: [])).")
    assertEquals(show("x = '{ p X :- q X, $..B }."), "x = '{ p X :- q X, $..B }.")
    assertEquals(show("x = '{p X, q X}."), "x = '{ p X, q X }.")
    assertEquals(show("x = '{ a. @r b :- c. ?- b. }."), "x = '{ a. @r b :- c. ?- b. }.")
    assertEquals(show("x = ['{ p X :- q X, r X }]."), "x = ['{ p X :- q X, r X }].")
    assertEquals(show("x = f '{ X + 1 } '{}."), "x = f '{ (X + 1) } '{ }.")
    assertEquals(show("f '{ $R $X } = '{ $F[V] }."), "f '{ $R $X } = '{ $F[V] }.")
    // a prime inside or after a name is part of it: only `'` at the start of a token, before `{`, quotes
    assertEquals(show("x' = f' '{ g' }."), "x' = f' '{ g' }.")
    // with a space, `[V]` is not the argument list of a higher-order hole
    assertEquals(show("f X = $F [V]."), "f X = $F [V].")
  }

  private val decls =
    """n : type.
      |z : n.
      |s : n -> n.
      |num : n -> rel.
      |p : n -> int -> rel.
      |q : int -> string -> rel.
      |r : int -> rel.
      |w : float -> rel.
      |""".stripMargin

  private val rules = List(
    "num z.",
    "num (s X) :- X = z, not w 2.0.",
    "q K \"x\" :- p _ K, K >= 1, K <= 2 ; K = -1 * 2.",
    "r N :- N = count { V | num V }.",
    "r M :- M = sum { K * 2 | p _ K }, M <> 0.",
    "p X 1 :- num X, X = z.",
    "w 1.5.",
    "num X, r 1 :- p X 2."
  )

  private def quoted(rule: String): String = "'{ " + rule + " }"

  private def staged(code: String): String =
    val c = TestSupport.compile(code, Settings(stopAfter = Some("stage")))
    assert(!c.reporter.hasErrors, c.reporter.diagnostics.map(_.message).mkString("\n"))
    ObjPrinter.program(c.unit.prog.nn).replaceAll("#\\d+", "")

  test("reflect ∘ reify = id: quoted rules reflected are the rules written directly (up to renaming)") {
    for rule <- rules do assertEquals(staged(decls + "$[" + quoted(rule) + "]."), staged(decls + rule), rule)
  }

  private lazy val prelude =
    scala.io.Source.fromResource("hugin/stdlib/prelude.hgn").mkString

  private def withoutPositions(t: Tm): Tm = Tm.mapChildren(Tm.unloc(t))(withoutPositions)

  private def elements(t: Tm): List[Tm] = t match
    case Tm.App(Tm.App(Tm.App(_, _, Icit.Impl), x, Icit.Expl), rest, Icit.Expl) => x :: elements(rest)
    case _ => Nil

  test("reify ∘ reflect = id: reflected data quoted again is the same data") {
    val e = CoreTesting.ok(prelude + decls + rules.mkString("data : module = '{ ", " ", " }."))
    val v = e.global("data").kind match
      case GlobalKind.Definition(_, v) => v
      case other => fail(s"not a definition: $other")
    val items = e.elab.reflectedItems(v, RKind.List(RKind.Item), Span.NoSpan)
    assertEquals(items.length, rules.length)
    val again = items.map {
      case r: Rule => e.elab.reify(Cxt.empty, Quote(List(r), true)(Span.NoSpan), RKind.Item)
      case other => fail(s"not a rule: $other")
    }
    val original = elements(withoutPositions(e.core.quote(0, v)))
    for (a, b) <- original.zip(again) do
      assertEquals(withoutPositions(e.core.nf(Nil, b)), a, e.core.showTm(Nil, a))
  }

  private val program =
    """node : type.
      |a : node.
      |b : node.
      |edge : node -> node -> rel.
      |m = { edge : node -> node -> rel. }.
      |isEdge : formula -> int.
      |isEdge '{ edge $X $Y } = 1.
      |isEdge _ = 0.
      |flip : formula -> formula.
      |flip '{ $R $X $Y } = '{ $R $Y $X }.
      |flip F = F.
      |size : formula -> int.
      |size '{ $F, $G } = size F + size G.
      |size _ = 1.
      |body : formula -> formula.
      |body '{ N = count { V | $F[V] } } = F (tvar "W").
      |body G = G.
      |""".stripMargin

  test("matching resolves names to symbols: a shadowing `edge` does not match") {
    val e = CoreTesting.ok(prelude + program)
    assertEquals(e.eval("isEdge '{ edge a b }"), "1")
    assertEquals(e.eval("isEdge '{ m.edge a b }"), "0")
    assertEquals(e.eval("isEdge '{ edge a b, edge b a }"), "0")
  }

  test("quoted patterns: holes in relation position, higher-order holes for aggregates") {
    val e = CoreTesting.ok(prelude + program)
    assertEquals(e.eval("isEdge (flip '{ edge a b })"), "1")
    assertEquals(e.eval("size '{ edge a b, edge b a, edge b b }"), "3")
    // the body of the aggregate with its bound variable instantiated by `W`
    val opened = e.eval("body '{ N = count { V | edge V a, edge a V } }")
    assert(opened.startsWith("fconj (fatom ⟨edge⟩ (cons {term} (tvar \"W\")"), opened)
  }

  test("quoted patterns are checked for coverage and termination") {
    assertEquals(CoreTesting.errors(prelude + "isEdge : formula -> int.\nisEdge '{ not $F } = 1."), List("E0911"))
    assertEquals(CoreTesting.errors(prelude + "f : formula -> int.\nf '{ not $F } = f '{ not $F }.\nf _ = 0."), List("E0912"))
  }
