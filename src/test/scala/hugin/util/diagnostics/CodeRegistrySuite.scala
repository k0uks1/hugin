package hugin.util.diagnostics

/** The registry `Code`: unique ids, numbering by phase, lint names. */
class CodeRegistrySuite extends munit.FunSuite:
  private val codes = Code.values.toList

  test("ids are unique") {
    assertEquals(codes.map(_.id).distinct, codes.map(_.id))
  }

  test("each case is named by its id") {
    for c <- codes do assertEquals(c.toString, c.id)
  }

  test("numbers are sorted within each phase") {
    for (phase, cs) <- Code.byPhase do assertEquals(cs.map(_.number), cs.map(_.number).sorted, s"phase $phase")
  }

  test("error codes lie in their phase's block, and none in the block reserved for user directives") {
    for c <- codes if c.lint.isEmpty do
      assertEquals(c.number / 100, c.phase.block, s"${c.id} is not in the block of ${c.phase}")
      assert(!Code.userDirectiveNumbers.contains(c.number), s"${c.id} lies in the range reserved for user directives")
  }

  test("warnings are lints with distinct names, and lints are warnings") {
    val lints = codes.filter(_.lint.isDefined)
    assert(lints.forall(_.level != Level.Error))
    assert(lints.forall(_.phase == Phase.Lints))
    assertEquals(lints.flatMap(_.lint).distinct.length, lints.length)
    assert(codes.filter(_.lint.isEmpty).forall(_.level == Level.Error))
  }

  test("codes parse back from their ids, case-insensitively") {
    for c <- codes do
      assertEquals(Code.parse(c.id), Some(c))
      assertEquals(Code.parse(c.id.toLowerCase), Some(c))
    assertEquals(Code.parse("E9999"), None)
  }

  test("every active code is explained, and the inventory lists every code") {
    for c <- codes if c.isActive do assert(Explanations.explain(c.id).exists(_.startsWith(s"# ${c.id}: ${c.title}")), c.id)
    for c <- codes do assert(Explanations.inventory.contains(s"${c.id}  ${c.title}"), c.id)
  }
