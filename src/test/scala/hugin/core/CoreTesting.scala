package hugin.core

import hugin.util.*

/** Helpers for the tests of the new meta level: elaborating programs given as strings, and building core
 *  terms directly. */
object CoreTesting:
  final case class Elaborated(core: Core, elab: hugin.core.elab.Elaborator, diagnostics: List[Diagnostic], output: List[String]):
    def errors: List[String] = diagnostics.filter(_.severity == Severity.Error).flatMap(_.code)
    def global(n: String): GlobalEntry = core.globals(elab.scope(n))

    /** The declared type of a global, printed. */
    def typeOf(n: String): String = core.showTm(Nil, core.zonk(Nil, 0, global(n).tyTm))

    /** The elaborated definition of a global, printed (with inserted quotes, splices, implicits). */
    def termOf(n: String): String = global(n).kind match
      case GlobalKind.Definition(tm, _) => core.showTm(Nil, tm)
      case k => s"<$k>"

    /** The normal form of a global's definition. */
    def nfOf(n: String): String = global(n).kind match
      case GlobalKind.Definition(_, v) => core.showVal(Nil, v)
      case k => s"<$k>"

    /** The normal form of an expression elaborated (with inferred type) in the program's scope. */
    def eval(expr: String): String =
      val src = SourceFile.virtual("expr.hgn", s"it = $expr.")
      val r = Reporter()
      val items = hugin.syntax.Parser.parseMeta2(src, r).items
      items.foreach(elab.elabItemReporting)
      assert(!r.hasErrors && !reporterErrors, s"errors in $expr: ${elab.reporter.diagnostics.map(_.message)}")
      val v = global("it").kind match
        case GlobalKind.Definition(_, v) => core.showVal(Nil, v)
        case _ => "?"
      elab.scope.remove("it")
      v

    private def reporterErrors: Boolean = elab.reporter.diagnostics.exists(_.severity == Severity.Error)

  def elaborate(code: String): Elaborated =
    val reporter = Reporter()
    val prog = hugin.syntax.Parser.parseMeta2(SourceFile.virtual("test.hgn", code), reporter)
    val core = Core()
    val elab = hugin.core.elab.Elaborator(core, reporter)
    if !reporter.hasErrors then elab.elabProgram(prog.items)
    val out = if reporter.hasErrors then Nil else Staging(core, reporter).render(elab.items.toList)
    Elaborated(core, elab, reporter.sorted, out)

  /** Elaborates and fails the test on errors. */
  def ok(code: String): Elaborated =
    val e = elaborate(code)
    val renderer = DiagnosticRenderer(color = false)
    assert(e.errors.isEmpty, e.diagnostics.map(renderer.render).mkString("\n"))
    e

  /** The error codes of a program. */
  def errors(code: String): List[String] = elaborate(code).errors

  /** The first rendered error of a program. */
  def firstError(code: String): String =
    elaborate(code).diagnostics.find(_.severity == Severity.Error).map(DiagnosticRenderer(color = false).render).getOrElse("")
