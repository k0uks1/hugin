package hugin.cli

class CommandLineSuite extends munit.FunSuite:
  test("commands and options are parsed") {
    val o = CommandLine.parse(List("run", "a.hgn", "--facts", "x.facts", "--facts", "y.facts")).toOption.get
    assertEquals(o.command, Command.Run("a.hgn"))
    assertEquals(o.run.facts, List("x.facts", "y.facts"))
    assert(!o.settings.explainTermination)
    assert(CommandLine.parse(List("check", "a.hgn", "--explain-termination")).toOption.get.settings.explainTermination)
  }

  test("phase names are validated") {
    assert(CommandLine.parse(List("check", "a.hgn", "--print-after", "elaborate,derivations")).isRight)
    assertEquals(CommandLine.parse(List("check", "a.hgn", "--stop-after", "nope")), Left("unknown phase `nope`; see `hugin phases`"))
  }

  test("malformed command lines are rejected with a message") {
    assert(CommandLine.parse(List("run", "a.hgn", "--budget", "3")).left.exists(_.contains("--budget"))) // removed with %partial
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

  test("lint levels and fix are parsed; --no-warnings is gone") {
    import hugin.util.diagnostics.{Level, Lint}
    val o = CommandLine.parse(List("check", "a.hgn", "-A", "singleton_variables", "--deny", "W0003", "--deny-warnings")).toOption.get
    assertEquals(o.display.lints.level(Lint.SingletonVariables), Level.Allow)
    assertEquals(o.display.lints.level(Lint.UnusedDefinitions), Level.Error)
    assert(o.display.lints.denyWarnings)
    assertEquals(CommandLine.parse(List("check", "a.hgn", "-W", "nope")), Left("unknown lint `nope`; see `hugin explain --list`"))
    assert(CommandLine.parse(List("check", "a.hgn", "--no-warnings")).isLeft)
    assertEquals(CommandLine.parse(List("fix", "a.hgn")).map(_.command), Right(Command.Fix("a.hgn")))
  }
