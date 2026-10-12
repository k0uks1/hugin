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

  /** The program-dependent declarations of a file (#186 P9f), by name, with their chains. */
  private def phase(code: String): (List[String], Map[String, List[String]]) =
    val items = hugin.syntax.Parser.parse(SourceFile.virtual("test.hgn", code), Reporter()).items
    val (_, deferred) = hugin.core.elab.ProgramPhase.classify(
      items,
      programOfFree = true,
      {
        case Directive(_, _: DirArgs.Use) => false
        case _ => true
      }
    )
    def name(i: Item): String = i match
      case d: Decl => d.name.name
      case d: Def => d.name.name
      case c: Clause => hugin.syntax.TreeOps.headName(c.lhs).fold("?")(_.name)
      case d: Directive => s"%${d.kind}"
      case _ => "?"
    (deferred.items.map(name), deferred.chains)

  test("program-dependent declarations: `here` and what uses it, after the object items (#186 P9f)") {
    val (later, chains) = phase(
      """road : int -> int -> rel.
        |road 1 2.
        |p : program = programOf here.
        |n : int = 3.
        |count : program -> int.
        |count P = n.
        |size : int = count p.
        |lemma : {D : db} -> here ⊢[D] road 1 2 -> Type.
        |lemma _ = Type.
        |m = { q : int -> rel. stated : program = programOf here. }.
        |%opaque lemma n.
        |%use p.
        |""".stripMargin
    )
    // `count` and `n` mention no program; the body's `here` is its own; `%use` is never deferred
    assertEquals(later, List("p", "size", "lemma", "lemma", "%opaque"))
    assertEquals(
      chains,
      Map("p" -> List("p", "programOf here"), "size" -> List("size", "p", "programOf here"), "lemma" -> List("lemma", "here ⊢ …"))
    )
  }

  test("a file without `here` has no program-dependent declarations; `where` and `there` are not `here`") {
    val (later, _) = phase("x : int = 1.\nf : int -> int.\nf X = y where y = X.\nthere : int = x.\n")
    assertEquals(later, Nil)
  }

  test("`here` as the membership proof of `std/semantics` is not the program: nothing is deferred (#186 P9f)") {
    val (later, chains) = phase(
      """second : {A : Type} -> {x y : A} -> {xs : list A} -> member y (x :: y :: xs) = there here.
        |walk : {g : graph2} -> {d : db} -> {x y z : ⇑g.node} -> tcPath g d x z -> Type.
        |walk (fire {xs := econs X (econs Z enil)} (there here) (ppos refl E pnil) here) = Type.
        |walk (fire here Ps (there ())) = Type.
        |r : int -> rel.
        |r 1.
        |""".stripMargin
    )
    assertEquals(later, Nil)
    assertEquals(chains, Map.empty[String, List[String]])
  }

