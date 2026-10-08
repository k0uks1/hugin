package hugin

import hugin.compiler.*
import hugin.util.*

/** Helpers for compiling and running programs given as strings. */
object TestSupport:
  def compile(code: String, settings: Settings = Settings()): Context =
    Compiler.compile(SourceFile.virtual("test.hgn", code), settings, _ => ())

  def errorCodes(c: Context): List[String] =
    c.reporter.diagnostics.filter(_.severity == Severity.Error).map(_.code).map(_.id)

  /** Compiles and runs; returns the printed output lines, or the error codes. */
  def run(code: String, facts: String = "", settings: Settings = Settings()): Either[List[String], List[String]] =
    val c = compile(code, settings)
    if c.reporter.hasErrors then Left(errorCodes(c))
    else
      val factFiles = if facts.isEmpty then Nil else List(SourceFile.virtual("test.facts", facts))
      val outcome = hugin.runtime.Evaluation.run(c, factFiles)
      outcome.result match
        case Some(res) => Right(res.output)
        case None => Left(outcome.diagnostics.map(_.code).map(_.id))
