package hugin.compiler

import hugin.syntax.{Parser, Program, Trees}
import hugin.util.*
import java.nio.file.{Files, InvalidPathException, Path}
import scala.collection.mutable

/** A parsed source file with its parse diagnostics. */
final case class Parsed(source: SourceFile, program: Program, diagnostics: List[Diagnostic])

object Parsed:
  def apply(source: SourceFile): Parsed =
    val reporter = Reporter()
    val program = Parser.parse(source, reporter)
    Parsed(source, program, reporter.sorted)

/** Finds and parses the source files of imports and of the prelude. */
trait SourceLoader:
  /** The parsed file at a (resolved) path, or `None` if there is no such file. */
  def load(path: String): Option[Parsed]

object SourceLoader:
  /** Paths below this prefix denote the standard library bundled with the compiler. */
  val StdlibPrefix = "<stdlib>/"
  val PreludePath: String = StdlibPrefix + "prelude.hgn"

  /** The text of a bundled standard library file. */
  def stdlib(path: String): Option[String] =
    if !path.startsWith(StdlibPrefix) then None
    else
      Option(getClass.getResourceAsStream("/hugin/stdlib/" + path.stripPrefix(StdlibPrefix))).map { in =>
        try String(in.readAllBytes(), java.nio.charset.StandardCharsets.UTF_8)
        finally in.close()
      }

  /** The text of a file: the bundled standard library, or a file on disk. */
  def read(path: String): Option[String] =
    if path.startsWith(StdlibPrefix) then stdlib(path)
    else
      try
        val p = Path.of(path)
        if Files.isRegularFile(p) then Some(Files.readString(p)) else None
      catch case _: InvalidPathException => None

  /** Reads and parses files directly (the standard library's parses are shared, [[StdlibCache]]). */
  val files: SourceLoader = path => read(path).map(text => StdlibCache.parsed(path, text))

  /** Resolves an import path relative to the importing file; `.hgn` is appended if there is no extension.
   *  A path that is not a valid file path (a NUL character, characters the file system cannot encode, a
   *  root without a file name) is returned unchanged; loading it then fails with "cannot find". */
  def resolve(from: String, path: String): String =
    try
      val hasExt = Option(Path.of(path).getFileName).exists(_.toString.contains('.'))
      val withExt = if hasExt then path else path + ".hgn"
      val parent = Option(Path.of(from).getParent)
      parent.map(_.resolve(withExt)).getOrElse(Path.of(withExt)).normalize.toString
    catch case _: InvalidPathException => path

/** The import graph of a program, from a walk of its imports in depth-first order (the prelude's
 *  imports first): `files` are the files to include in dependency order (a file after the files it
 *  imports), `cut` the imports that closed a cycle per importing file, `missing` the resolved paths of
 *  imports that do not exist, `diagnostics` the parse diagnostics of the included files and E0108 for
 *  missing and cyclic imports. Which import of a cycle is reported (and cut) depends on where the walk
 *  enters the cycle, so the graph belongs to the program, not to the files. */
final case class ImportGraph(
    files: List[String],
    cut: Map[String, Set[String]],
    missing: Set[String],
    diagnostics: List[Diagnostic]
)

object ImportGraph:
  /** Walks the imports of `program` (the file `root`, or the files of its items if it is made of several),
   *  after the imports of the prelude if `prelude`. */
  def compute(root: String, program: Program, prelude: Boolean, libs: Libraries): ImportGraph =
    val files = mutable.ListBuffer.empty[String]
    val included = mutable.HashSet.empty[String]
    val missing = mutable.LinkedHashSet.empty[String]
    val cut = mutable.LinkedHashMap.empty[String, Set[String]]
    val diagnostics = mutable.ListBuffer.empty[Diagnostic]

    /** Loads the imports `imports` of the file `from`; `stack` lists the files being loaded. Files are
     *  added after their own imports. */
    def visit(from: String, imports: List[(Trees.Import, String)], stack: List[String]): Unit =
      for (imp, path) <- imports do
        if stack.contains(path) then
          val cycle = (path :: stack.takeWhile(_ != path).reverse) :+ path
          diagnostics += ImportError.Cycle(imp.path, imp.pathSpan, cycle).toDiagnostic
          cut(from) = cut.getOrElse(from, Set.empty) + path
        else if !included(path) && !missing(path) then
          libs.load(path) match
            case None =>
              missing += path
              diagnostics += ImportError.Missing(imp.path, imp.pathSpan, path).toDiagnostic
            case Some(p) =>
              diagnostics ++= p.diagnostics
              visit(path, libs.imports(path), path :: stack)
              if included.add(path) then files += path

    if prelude then
      libs.load(SourceLoader.PreludePath) match
        case Some(p) =>
          diagnostics ++= p.diagnostics
          visit(SourceLoader.PreludePath, libs.imports(SourceLoader.PreludePath), List(SourceLoader.PreludePath))
          if included.add(SourceLoader.PreludePath) then files += SourceLoader.PreludePath
        case None =>
          diagnostics += ImportError.PreludeMissing.toDiagnostic
    // a program made of several files (a REPL session) is being loaded as a whole: all its files
    val rootFiles = root :: program.items.map(_.span).filter(_.exists).map(_.source.path)
    val rootImports = ImportPaths.importsIn(program).map(i => (i, ImportPaths.resolve(i, root)))
    visit(root, rootImports, rootFiles.distinct.map(ImportPaths.normalize))
    ImportGraph(files.toList, cut.toMap, missing.toSet, diagnostics.toList)

/** Where a compilation gets its files from. The query database memoises them (see `hugin.query`), so that
 *  files are read and parsed once; [[Libraries.direct]] loads them once per instance. */
trait Libraries:
  /** The parsed file at a (resolved) path, or `None` if there is no such file. */
  def load(path: String): Option[Parsed]

  /** The `%import`s of a file that exists, with their resolved paths, in source order. */
  def imports(path: String): List[(Trees.Import, String)]

  /** The import graph of a program (see [[ImportGraph.compute]]). */
  def graph(root: String, program: Program, prelude: Boolean): ImportGraph

  /** Elaborates the program `program` (the file `root`) with the files of its import graph (the prelude
   *  first, if included). The query database computes it in memoised parts. */
  def elaborate(root: String, program: Program, graph: ImportGraph, prelude: Boolean): ProgramElaboration =
    hugin.core.MetaLevel.elaborateProgram(root, program, graph, prelude, load)

/** A program elaborated by the meta level: the result, its diagnostics and what it recorded for tooling. */
final class ProgramElaboration(
    val elaborated: hugin.core.Elaborated,
    val diagnostics: List[Diagnostic],
    val index: SemanticIndex
)

object Libraries:
  /** Loads everything from `loader`, each file once (per instance). */
  def direct(loader: SourceLoader): Libraries = new Libraries:
    private val loaded = mutable.HashMap.empty[String, Option[Parsed]]
    def load(path: String): Option[Parsed] = loaded.getOrElseUpdate(path, loader.load(path))
    def imports(path: String): List[(Trees.Import, String)] = Library.importsOf(path, load(path).get.program)
    def graph(root: String, program: Program, prelude: Boolean): ImportGraph = ImportGraph.compute(root, program, prelude, this)

/** A library file included in a compilation: the prelude or an imported file. */
final class Library(val path: String):
  def isPrelude: Boolean = path == SourceLoader.PreludePath

  /** Module name: the file name without extension (the qualifier of its object constants). */
  val name: String = Library.moduleName(path)

object Library:
  def moduleName(path: String): String = Path.of(path).getFileName.toString.takeWhile(_ != '.')

  /** The imported files (not the prelude) with the qualifiers of their object constants: their module
   *  names, numbered where they clash. */
  def qualified(files: List[String]): List[(String, String)] =
    val taken = mutable.HashSet("", "prelude")
    files.filterNot(_ == SourceLoader.PreludePath).map { path =>
      val base = moduleName(path)
      path -> Iterator.from(1).map(k => if k == 1 then base else s"$base$k").find(taken.add).get
    }

  /** The imports of the file `path` with their resolved paths. */
  def importsOf(path: String, program: Program): List[(Trees.Import, String)] =
    ImportPaths.importsIn(program).map(i => (i, ImportPaths.resolve(i, path)))

/** Resolving `%import` paths. */
object ImportPaths:
  private[compiler] def normalize(path: String): String =
    try Path.of(path).normalize.toString
    catch case _: InvalidPathException => path

  /** The resolved path of an import: relative to the file it is written in (the source of its span), or
   *  to `from` if it has no position. */
  def resolve(imp: Trees.Import, from: String): String =
    SourceLoader.resolve(if imp.pathSpan.exists then imp.pathSpan.source.path else from, imp.path)

  /** All `%import` expressions of a program, in source order. */
  def importsIn(program: Program): List[Trees.Import] =
    hugin.syntax.TreeOps.nodes(program.items).collect { case i: Trees.Import => i }.toList
