package hugin.meta

import hugin.TestSupport
import hugin.syntax.{Parser, Program}
import hugin.util.*
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** Stable keys (step 6 of `docs/INCREMENTALITY.md`): item and symbol keys survive edits elsewhere in the
 *  file, and no two symbols of a compilation share a key. */
class KeysSuite extends munit.FunSuite:
  private val path = "test.hgn"

  private def parse(text: String): Program = Parser.parse(SourceFile.virtual(path, text), Reporter())
  private def itemKeys(text: String): List[ItemKey] = ItemKey.assign(ScopeKey.File(path), parse(text).items)
  private def symKeys(text: String): Set[SymKey] = TestSupport.compile(text).unit.symKeys.all

  /** Whether a scope lies (transitively) within the item `k`. */
  private def within(sc: ScopeKey, k: ItemKey): Boolean = sc match
    case ScopeKey.File(_) => false
    case ScopeKey.Module(o, _) => o == k || within(o.scope, k)
    case ScopeKey.Local(o, _) => o == k || within(o.scope, k)
    case ScopeKey.Params(s) => within(s.scope, k)

  private val program =
    """city : type. berlin : city. paris : city.
      |road : city -> city -> rel.
      |reach : city -> city -> rel.
      |reach X Y :- road X Y.
      |reach X Z :- road X Y, reach Y Z.
      |@base reach X X :- road X _.
      |?- reach berlin X.
      |%input road.
      |""".stripMargin

  test("item keys ignore positions: blank lines and comments before an item keep its key") {
    val moved = "\n\n// a comment\n" + program.replace(".\n", ".\n\n")
    assertEquals(itemKeys(moved), itemKeys(program))
  }

  test("inserting an unrelated item keeps the keys of the other items") {
    val before = itemKeys(program)
    val after = itemKeys("other : type.\nroad other other.\n" + program)
    assertEquals(after.drop(2), before)
  }

  test("editing an anonymous rule changes only its own key") {
    val before = itemKeys(program)
    val after = itemKeys(program.replace("reach X Y :- road X Y.", "reach X Y :- road Y X."))
    val changed = before.zip(after).collect { case (b, a) if a != b => b }
    assertEquals(changed.length, 1)
    assert(changed.head.id.isInstanceOf[ItemId.Anon], changed)
  }

  test("identical items and redeclarations get distinct keys") {
    val keys = itemKeys("a : type.\na : type.\nr : rel.\nr.\nr.\n@x r.\n@x r.\n")
    assertEquals(keys.distinct.length, keys.length)
    assertEquals(keys.take(2).map(_.id), List(ItemId.Named("a", 0), ItemId.Named("a", 1)))
    assertEquals(keys.drop(5).map(_.id), List(ItemId.Rule("x", 0), ItemId.Rule("x", 1)))
  }

  test("the structural hash ignores spans, also those stored as fields") {
    val a = parse("s : type = { %mode p (+), p : int -> rel }.").items
    val b = parse("\n  s : type = {  %mode p (+),\n p : int -> rel }.").items
    assertEquals(ItemKey.structuralHash(a), ItemKey.structuralHash(b))
  }

  test("a key can be registered only once") {
    val keys = SymKeys()
    val k = SymKey(ScopeKey.File(path), "a")
    keys.register(k)
    intercept[AssertionError](keys.register(k))
  }

  test("symbols are equal by key across compilations") {
    val a = TestSupport.compile(program).unit.rootScope.nn.lookupLocal("road").get
    val b = TestSupport.compile("\n\n" + program).unit.rootScope.nn.lookupLocal("road").get
    assert(a ne b)
    assertEquals(a, b)
    assertEquals(a.hashCode, b.hashCode)
    assertNotEquals(a.span, b.span)
  }

  test("binders that shadow one another in the same scope get distinct keys") {
    val text =
      """p : (x : int) -> (x : int) -> prop.
        |p X Y :- X = Y.
        |id = [A : list A] A.
        |pair A A : type = A.
        |m = { a = 1, b = { a = 2 } }.
        |n = { a = 3 }.
        |""".stripMargin
    // compiling fails with an AssertionError if two symbols share a key
    symKeys(text)
  }

  private def goldenPrograms: List[Path] =
    List("run", "pos").flatMap { d =>
      Files.list(Path.of("tests", d)).iterator.asScala.filter(_.toString.endsWith(".hgn")).toList
    }.sortBy(_.toString)

  test("symbol keys of golden programs survive inserting an unrelated item before them") {
    val inserted = ItemKey(ScopeKey.File(path), ItemId.Named("zz_inserted", 0))
    for p <- goldenPrograms do
      val text = Files.readString(p)
      val before = symKeys(text)
      val after = symKeys("zz_inserted : int -> int = [x : int] x.\n\n" + text)
      assertEquals(before -- after, Set.empty[SymKey], s"keys lost in $p")
      val added = after -- before
      val unrelated = added.filterNot(k => k == SymKey(inserted.scope, "zz_inserted") || within(k.scope, inserted))
      assertEquals(unrelated, Set.empty[SymKey], s"keys added in $p")
  }
