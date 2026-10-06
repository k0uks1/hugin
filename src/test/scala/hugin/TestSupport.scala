package hugin

import hugin.compiler.*
import hugin.util.*

/** Helpers for compiling and running programs given as strings. */
object TestSupport:
  def compile(code: String, settings: Settings = Settings()): Context =
    Compiler.compile(SourceFile.virtual("test.hgn", code), settings, _ => ())

  def errorCodes(c: Context): List[String] =
    c.reporter.diagnostics.filter(_.severity == Severity.Error).flatMap(_.code)

  /** Compiles and runs; returns the printed output lines, or the error codes. */
  def run(code: String, facts: String = "", budget: Option[Int] = None): Either[List[String], List[String]] =
    val c = compile(code)
    if c.reporter.hasErrors then Left(errorCodes(c))
    else
      val factFiles = if facts.isEmpty then Nil else List(SourceFile.virtual("test.facts", facts))
      val outcome = hugin.runtime.Evaluation.run(c, factFiles, budget)
      outcome.result match
        case Some(res) => Right(res.output)
        case None => Left(outcome.diagnostics.flatMap(_.code))
