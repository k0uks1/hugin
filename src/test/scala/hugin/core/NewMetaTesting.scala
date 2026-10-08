package hugin.core

import hugin.TestSupport
import hugin.compiler.Settings
import hugin.obj.ObjPrinter

/** Compiling programs with the new meta level for the tests of B3: the staged object program, the error
 *  codes, the run's output. */
object NewMetaTesting:
  private val settings = Settings(newMeta = true)

  /** The object program after `stage`; fails on errors. */
  def staged(code: String, prelude: Boolean = true): String =
    val c = TestSupport.compile(code, settings.copy(prelude = prelude, stopAfter = Some("stage")))
    assert(!c.reporter.hasErrors, c.reporter.diagnostics.map(_.message).mkString("\n"))
    ObjPrinter.program(c.unit.prog.nn)

  /** The error codes of compiling the program. */
  def errors(code: String): List[String] = TestSupport.errorCodes(TestSupport.compile(code, settings))

  /** The output of running the program (or its error codes). */
  def run(code: String): Either[List[String], List[String]] = TestSupport.run(code, settings = settings)
