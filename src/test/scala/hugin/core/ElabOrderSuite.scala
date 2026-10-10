package hugin.core

import hugin.core.elab.ElabOrder
import hugin.syntax.Trees.*
import hugin.util.{Reporter, SourceFile}

/** The dependency order of a file's declarations (issue #91, reference: meta/index, "Order of
 *  elaboration"): components in topological order, independent ones in source order. */
class ElabOrderSuite extends munit.FunSuite:

  /** The components of a program, each as the names of its nodes (`f` for a plain item, `f=` for the
   *  clauses of `f`). */
  private def order(code: String): List[List[String]] =
    val items = hugin.syntax.Parser.parse(SourceFile.virtual("test.hgn", code), Reporter()).items
    val declared = items.collect { case d: Decl => d.name.name }.toSet
    def clauseName(i: Item): Option[String] = i match
      case Clause(lhs, _, _) => hugin.syntax.TreeOps.headName(lhs).map(_.name)
      case d: Def if declared(d.name.name) => Some(d.name.name)
      case _ => None
    val (clauses, plain) = items.partition(clauseName(_).isDefined)
    val groups = clauses.groupBy(clauseName(_).get).toList.sortBy(_._2.head.span.start)
    def names(i: Item) = i match
      case d: Decl => List(d.name.name)
      case d: Def => List(d.name.name)
      case _ => Nil
    val plan = ElabOrder.plan(ElabOrder.Input(plain.map(i => (i, names(i))), groups, Nil, None, Set.empty, _ => true))
    plan.components.map(_.map { i =>
      val n = plan.nodes(i)
      n.kind match
        case ElabOrder.Kind.Clauses(f) => s"$f="
        case _ => names(n.items.head).mkString
    })

  test("the issue: a function's signature and clauses before the definitions that compute with it") {
    val got = order(
      """nat : Type. zero : nat. suc : nat -> nat.
        |one : nat = suc zero.
        |vec3 : Type = vec int (plus one (suc one)).
        |v : vec3 = vcons 1 (vcons 2 (vcons 3 vnil)).
        |plus : nat -> nat -> nat.
        |plus zero N = N.
        |plus (suc M) N = suc (plus M N).
        |vec : Type -> nat -> Type.
        |vnil : vec A zero.
        |vcons : A -> vec A N -> vec A (suc N).
        |""".stripMargin
    )
    assertEquals(
      got.flatten,
      List("nat", "zero", "suc", "one", "plus", "plus=", "vec", "vec3", "vnil", "vcons", "v")
    )
    assert(got.forall(_.length == 1), got)
  }

  test("a definition and a function that refer to each other are one component") {
    val got = order(
      """nat : Type. zero : nat. suc : nat -> nat.
        |d : vec int (k zero) = vcons 1 vnil.
        |k : nat -> nat.
        |k zero = zero.
        |k (suc N) = vlen d.
        |vlen : vec A N -> nat.
        |vec : Type -> nat -> Type.
        |vnil : vec A zero.
        |vcons : A -> vec A N -> vec A (suc N).
        |""".stripMargin
    )
    assert(got.contains(List("d", "k=")), got)
    assert(got.indexOf(List("k")) < got.indexOf(List("d", "k=")), got)
  }

  test("mentions leave out the item's own name, labels and binders") {
    val items = hugin.syntax.Parser.parse(
      SourceFile.virtual("test.hgn", "g : Type = { node : type, edge : node -> node -> rel }.\nh (x : int) = [y] { a = y }.\n"),
      Reporter()
    ).items
    val g = ElabOrder.mentions(items(0))
    assert(!g("g") && !g("edge") && g("node"), g)
    val h = ElabOrder.mentions(items(1))
    assert(!h("h") && !h("a") && h("int"), h)
  }
