package hugin.query

import hugin.compiler.SemanticIndex.Stage

/** Hover over staged code (quoted, spliced, persisted) and over uses and declarations of families. */
class StagingHoverSuite extends munit.FunSuite:
  private val program =
    """item : (name : string) -> (price : int) -> rel.
      |listed : item -> rel.
      |%input listed.
      |cheap : item -> prop = [I] I.price < 10.
      |select (p : A -> prop) (r : A -> rel) = {
      |  sel : A -> rel.
      |  @s sel X :- r X, p X.
      |}.
      |bargains = select cheap listed.
      |k : int = 6 * 7.
      |at_k : int -> rel.
      |at_k X :- X = k.
      |window (lo : int) = {
      |  above : int -> rel.
      |  above X :- at_k X, X > lo.
      |}.
      |w1 = window 1.
      |w2 = window 2.
      |nums : list int -> rel.
      |nums (cons 1 (cons 2 nil)).
      |words : list string -> rel.
      |words (cons "a" nil).
      |?- nums L, len L N.
      |?- words L, len L N.
      |""".stripMargin

  private val key = CompileKey("s.hgn")

  private given db: Database =
    val d = Database()
    d.set(SourceText, "s.hgn", program)
    d

  /** Offset of the `n`-th occurrence (0-based) of `needle`, plus `shift`. */
  private def at(needle: String, shift: Int = 0, n: Int = 0): Int =
    Iterator.iterate(program.indexOf(needle))(i => program.indexOf(needle, i + 1)).drop(n).next() + shift

  private def hover(offset: Int): HoverInfo = Ide.hoverInfo(key, offset).getOrElse(fail(s"no hover at $offset"))

  test("the program compiles without errors") {
    assertEquals(Ide.diagnostics(key).filter(_.severity == hugin.util.Severity.Error), Nil)
  }

  test("a compile-time primitive in object code is persisted as a literal") {
    val h = hover(at("X = k", "X = ".length))
    assertEquals(h.signature, Some("meta definition k : int"))
    assertEquals(h.notes, List("persisted: the compile-time value `42` is embedded as a literal"))
  }

  test("a parameter persisted in several applications shows every value") {
    val h = hover(at("X > lo", "X > ".length))
    assertEquals(h.signature, Some("meta parameter lo : int"))
    assertEquals(h.notes, List("persisted: the compile-time value `1` | `2` is embedded as a literal  (in different applications)"))
  }

  test("code passed to a formula function is quoted, and spliced into its body") {
    val arg = hover(at("p X", "p ".length))
    assertEquals(arg.signature, Some("variable X : item"))
    assertEquals(arg.notes, List("quoted: passed to the meta level as the code `X`"))
    val use = hover(at("I.price"))
    assertEquals(use.notes, List("spliced: the meta-level code `X` is inserted here"))
  }

  test("an applied formula function is spliced; its body is quoted") {
    val call = hover(at("p X"))
    assertEquals(call.signature, Some("meta parameter p : ⇑A -> ⇑prop"))
    assertEquals(call.notes, List("spliced: the meta-level code `X.price < 10` is inserted here"))
    // `<` itself names nothing: the hover only says how the formula is staged
    val body = hover(at("< 10"))
    assertEquals(body.signature, None)
    assertEquals(body.notes, List("quoted: passed to the meta level as the code `X.price < 10`"))
  }

  test("object code outside meta code has no staging notes") {
    assertEquals(hover(at("nums L")).notes, Nil)
    assertEquals(hover(at("at_k X :-", "at_k ".length)).notes, Nil)
  }

  test("a use of a family shows the instance it resolved to") {
    assertEquals(hover(at("cons 1")).notes, List("instance: `cons[int]`"))
    assertEquals(hover(at("cons 2")).notes, List("instance: `cons[int]`"))
    assertEquals(hover(at("nil))")).notes, List("instance: `nil[int]`"))
    assertEquals(hover(at("cons \"a\"")).notes, List("instance: `cons[string]`"))
    val len = hover(at("len L N", n = 1))
    assertEquals(len.signature, Some("relation len A : (l : list A) -> (n : int) -> rel"))
    assertEquals(len.notes, List("instance: `len[string]`"))
    // the argument of a family use is not itself the family
    assertEquals(Ide.hoverInfo(key, at("cons 1", "cons ".length)), None)
  }

  test("a family declared in the program lists its instances at the declaration") {
    val text = "box A : type.\nput : A -> box A.\nb : box int -> rel.\nb (put 1).\nc : box string -> rel.\nc (put \"x\").\n"
    given d: Database = Database()
    d.set(SourceText, "f.hgn", text)
    val k = CompileKey("f.hgn")
    assertEquals(Ide.hoverInfo(k, text.indexOf("box"))(using d).map(_.notes), Some(List("instances: `box[int]`, `box[string]`")))
    assertEquals(Ide.hoverInfo(k, text.indexOf("put"))(using d).map(_.notes), Some(List("instances: `put[int]`, `put[string]`")))
    assertEquals(Ide.hover(k, text.indexOf("put 1"))(using d), Some("constructor put A : A -> box A\ninstance: `put[int]`"))
  }

  test("the semantic index records staging by span") {
    val stages = db(Compile, key).index.staging.filter(_.span.source.path == "s.hgn").map(_.stage).toSet
    assertEquals(stages, Set(Stage.Quoted, Stage.Spliced, Stage.Persisted))
  }
