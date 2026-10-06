package hugin.cli

class CommandLineSuite extends munit.FunSuite:
  test("commands and options are parsed") {
    val o = CommandLine.parse(List("run", "a.hgn", "--facts", "x.facts", "--facts", "y.facts", "--budget", "3", "--lint")).toOption.get
    assertEquals(o.command, Command.Run("a.hgn"))
    assertEquals(o.run.facts, List("x.facts", "y.facts"))
    assertEquals(o.run.budget, Some(3))
    assert(o.settings.lint)
    assert(!o.settings.explainTermination)
    assert(CommandLine.parse(List("check", "a.hgn", "--explain-termination")).toOption.get.settings.explainTermination)
  }

  test("phase names are validated") {
    assert(CommandLine.parse(List("check", "a.hgn", "--print-after", "typer,demand")).isRight)
    assertEquals(CommandLine.parse(List("check", "a.hgn", "--stop-after", "nope")), Left("unknown phase `nope`; see `hugin phases`"))
  }

  test("malformed command lines are rejected with a message") {
    assertEquals(CommandLine.parse(List("run", "a.hgn", "--budget", "-1")), Left("--budget expects a natural number, got `-1`"))
    assert(CommandLine.parse(List("run", "a.hgn", "--frob")).left.exists(_.contains("--frob")))
    assert(CommandLine.parse(List("run", "a.hgn", "--facts")).left.exists(_.contains("--facts")))
    assert(CommandLine.parse(List("run")).isLeft)
    assertEquals(CommandLine.parse(Nil), Left("no command given"))
    assertEquals(CommandLine.parse(List("--help")).map(_.command), Right(Command.Help))
  }

  test("exit codes distinguish usage errors from compilation errors") {
    assertEquals(Main.run(List("check"), _ => (), _ => ()), ExitCode.Usage)
    assertEquals(Main.run(List("check", "does/not/exist.hgn"), _ => (), _ => ()), ExitCode.Usage)
    assertEquals(Main.run(List("explain", "E0401"), _ => (), _ => ()), ExitCode.Ok)
  }
