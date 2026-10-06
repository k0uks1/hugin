package hugin.query

import hugin.compiler.*
import hugin.runtime.Evaluation
import hugin.util.*
import scala.collection.mutable

/** The text of a file, by path: the only input of the compiler. Programs, imported files and facts files
 *  alike. A file that was never set is read on first use: the bundled standard library for `<stdlib>/`
 *  paths, otherwise the file on disk; clients that track changes (an editor) set the text explicitly. */
object SourceText extends Input[String, String]("sourceText"):
  override def default(path: String): Option[String] = SourceLoader.read(path)

/** Parses a file. */
object Parse extends Query[String, Parsed]("parse"):
  def compute(path: String)(using db: Database): Parsed = Parsed(SourceFile.virtual(path, db.get(SourceText, path)))

/** The `%import`s of a file with their resolved paths. The parsed source is part of the value so that an
 *  edit of the file is a change even when the imports are equal up to positions (trees compare without
 *  their spans). */
final case class FileImports(source: SourceFile, imports: List[(hugin.syntax.Trees.Import, String)])

object Imports extends Query[String, FileImports]("imports"):
  def compute(path: String)(using db: Database): FileImports =
    val parsed = db(Parse, path)
    FileImports(parsed.source, Library.importsOf(path, parsed.program))

final case class GraphKey(root: String, prelude: Boolean)

/** The import graph of a program ([[ImportGraph]]): recomputed when the program changes, cut off when its
 *  imports stay the same. */
object LibraryGraph extends Query[GraphKey, ImportGraph]("libraryGraph"):
  def compute(key: GraphKey)(using db: Database): ImportGraph =
    ImportGraph.compute(key.root, db(ParseProgram, key.root).program, key.prelude, DatabaseLibraries())

/** Diagnostics of the libraries, accumulated by the queries that name and elaborate them (a compilation
 *  reports the diagnostics of the libraries it includes from their results). */
object LibraryDiagnostics extends Accumulator[Diagnostic]("libraryDiagnostics")

/** Names a library file (the prelude or an imported file), once per revision of its text and of the
 *  prelude's; shared by all programs. */
object NameLibrary extends Query[NameKey, NamedLibrary]("nameLibrary"):
  def compute(key: NameKey)(using db: Database): NamedLibrary =
    val named = Library.name(key, DatabaseLibraries())
    named.diagnostics.foreach(db.push(LibraryDiagnostics, _))
    named

/** Elaborates a library file, once per revision of the files it depends on (its text, the prelude and
 *  the files it imports, transitively); shared by all programs. The keys never form a cycle: the import
 *  graph cuts every import that closes one (see [[LibraryKey]]). */
object ElabLibrary extends Query[LibraryKey, ElaboratedLibrary]("elabLibrary"):
  def compute(key: LibraryKey)(using db: Database): ElaboratedLibrary =
    val elaborated = Library.elaborate(key, DatabaseLibraries())
    elaborated.diagnostics.foreach(db.push(LibraryDiagnostics, _))
    elaborated

/** Loads files and libraries through the database, so that files are parsed, and libraries named and
 *  elaborated, once, and an edit of a file invalidates exactly what depends on it. */
private final class DatabaseLibraries(using db: Database) extends Libraries:
  def load(path: String): Option[Parsed] = if db.has(SourceText, path) then Some(db(Parse, path)) else None
  def imports(path: String): List[(hugin.syntax.Trees.Import, String)] = db(Imports, path).imports
  def graph(root: String, program: hugin.syntax.Program, prelude: Boolean): ImportGraph =
    // the graph of the program being compiled is memoised; another program (not from `ParseProgram`) is walked
    if db(ParseProgram, root).program eq program then db(LibraryGraph, GraphKey(root, prelude))
    else ImportGraph.compute(root, program, prelude, this)
  def named(key: NameKey): NamedLibrary = db(NameLibrary, key)
  def elaborated(key: LibraryKey): ElaboratedLibrary = db(ElabLibrary, key)

/** A file of a program made of several files ([[Composite]]); its queries are left out unless `queries`. */
final case class Part(path: String, queries: Boolean = true)

/** The files of a program that is not one file, such as a REPL session (its inputs and loaded files): the
 *  items of the parts, in order, form one module body. A path without this input is a file of its own. */
object Composite extends Input[String, Vector[Part]]("composite")

/** Parses a program: the file at `path`, or the parts set as its [[Composite]]. The items of a part keep
 *  their own source file, so their diagnostics point into it and their `%import`s resolve relative to it. */
object ParseProgram extends Query[String, Parsed]("parseProgram"):
  def compute(path: String)(using db: Database): Parsed =
    if !db.has(Composite, path) then db(Parse, path)
    else
      val parts = db.get(Composite, path).map(p => (p, db(Parse, p.path)))
      val items = parts.toList.flatMap((p, parsed) =>
        if p.queries then parsed.program.items else parsed.program.items.filterNot(_.isInstanceOf[hugin.syntax.Trees.Query])
      )
      Parsed(SourceFile.virtual(path, ""), hugin.syntax.Program(items, Span.NoSpan), parts.toList.flatMap(_._2.diagnostics))

final case class CompileKey(path: String, settings: Settings = Settings())

/** The result of compiling a program: the compilation context (unit, semantic index, diagnostics) and
 *  the output of `--print-after`. Treated as immutable once computed. */
final class Compiled(val context: Context, val printed: List[String]):
  def diagnostics: List[Diagnostic] = context.reporter.sorted
  def hasErrors: Boolean = context.reporter.hasErrors
  def index: SemanticIndex = context.unit.index

  /** The typing results of the meta level. */
  def symbols: hugin.meta.TypingResults = context.unit.symbols
  def source: SourceFile = context.unit.source

/** Runs the compiler pipeline on a parsed program. */
object Compile extends Query[CompileKey, Compiled]("compile"):
  def compute(key: CompileKey)(using db: Database): Compiled =
    val printed = mutable.ListBuffer.empty[String]
    val ctx = Compiler.compileWith(db(ParseProgram, key.path), key.settings, DatabaseLibraries(), printed += _)
    Compiled(ctx, printed.toList)

final case class EvaluateKey(compile: CompileKey, facts: List[String] = Nil, budget: Option[Int] = None, allRelations: Boolean = false)

/** Evaluates a compiled program over input facts. Changing only a facts file re-evaluates without
 *  recompiling; an evaluation with an unchanged outcome does not invalidate its dependents. */
object Evaluate extends Query[EvaluateKey, Evaluation.Outcome]("evaluate"):
  def compute(key: EvaluateKey)(using db: Database): Evaluation.Outcome =
    val compiled = db(Compile, key.compile)
    val facts = key.facts.map(f => SourceFile.virtual(f, db.get(SourceText, f)))
    Evaluation.run(compiled.context, facts, key.budget, key.allRelations)
