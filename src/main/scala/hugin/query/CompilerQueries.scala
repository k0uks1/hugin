package hugin.query

import hugin.compiler.*
import hugin.runtime.Evaluation
import hugin.syntax.{Parser, Program}
import hugin.util.*
import scala.collection.mutable

/** The text of a file, by path: the only input of the compiler. Programs and facts files alike. */
object SourceText extends Input[String, String]("sourceText")

/** The result of parsing one file. */
final class Parsed(val source: SourceFile, val program: Program, val diagnostics: List[Diagnostic])

/** Parses a file. */
object Parse extends Query[String, Parsed]("parse"):
  def compute(path: String)(using db: Database): Parsed =
    val source = SourceFile.virtual(path, db.get(SourceText, path))
    val reporter = Reporter()
    val program = Parser.parse(source, reporter)
    Parsed(source, program, reporter.sorted)

final case class CompileKey(path: String, settings: Settings = Settings())

/** The result of compiling a program: the compilation context (unit, semantic index, diagnostics) and
 *  the output of `--print-after`. Treated as immutable once computed. */
final class Compiled(val context: Context, val printed: List[String]):
  def diagnostics: List[Diagnostic] = context.reporter.sorted
  def hasErrors: Boolean = context.reporter.hasErrors
  def index: SemanticIndex = context.unit.index
  def source: SourceFile = context.unit.source

/** Runs the compiler pipeline on a parsed file. */
object Compile extends Query[CompileKey, Compiled]("compile"):
  def compute(key: CompileKey)(using db: Database): Compiled =
    val parsed = db(Parse, key.path)
    val printed = mutable.ListBuffer.empty[String]
    val ctx = Compiler.compileParsed(parsed.source, Some((parsed.program, parsed.diagnostics)), key.settings, printed += _)
    Compiled(ctx, printed.toList)

final case class EvaluateKey(compile: CompileKey, facts: List[String] = Nil, budget: Option[Int] = None, allRelations: Boolean = false)

/** Evaluates a compiled program over input facts. Changing only a facts file re-evaluates without
 *  recompiling; an evaluation with an unchanged outcome does not invalidate its dependents. */
object Evaluate extends Query[EvaluateKey, Evaluation.Outcome]("evaluate"):
  def compute(key: EvaluateKey)(using db: Database): Evaluation.Outcome =
    val compiled = db(Compile, key.compile)
    val facts = key.facts.map(f => SourceFile.virtual(f, db.get(SourceText, f)))
    Evaluation.run(compiled.context, facts, key.budget, key.allRelations)
