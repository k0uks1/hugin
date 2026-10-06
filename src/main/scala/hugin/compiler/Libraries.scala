package hugin.compiler

import hugin.meta.{MExpr, Scope, ScopeKey, Sym, SymKeys, SymTable}
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

  /** Reads and parses files directly (no caching). */
  val files: SourceLoader = path => read(path).map(text => Parsed(SourceFile.virtual(path, text)))

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

/** Identifies the naming of a library file: its path, and whether the prelude encloses its scope. */
final case class NameKey(path: String, prelude: Boolean):
  /** Whether the file is the prelude of the compilation (and not a file that merely has its path). */
  def isPrelude: Boolean = prelude && path == SourceLoader.PreludePath

/** Identifies the elaboration of a library file. A file is elaborated against the files it imports; an
 *  import that closes a cycle is left out (it denotes the erroneous module, E0108), so the result depends
 *  on which imports were cut: `cut` maps a file to the imports cut in it by the walk of the import graph
 *  ([[ImportGraph]]). It is empty for an acyclic graph, so that every compilation importing the file,
 *  whatever its other imports, shares one elaboration. */
final case class LibraryKey(path: String, prelude: Boolean, cut: Map[String, Set[String]] = Map.empty):
  def nameKey: NameKey = NameKey(path, prelude)
  def isPrelude: Boolean = nameKey.isPrelude

  /** The key of a file this one imports, with the same cuts; the prelude's elaboration has no imports. */
  def at(other: String): LibraryKey =
    if NameKey(other, prelude).isPrelude then LibraryKey(other, prelude) else copy(path = other)

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
          diagnostics += Diagnostic.error("E0108", s"cyclic import of `${imp.path}`", imp.pathSpan, "imported here")
            .withNote(s"import cycle: ${cycle.mkString(" -> ")}")
            .withHelp("a file is a module body; move what both files need into a third file")
          cut(from) = cut.getOrElse(from, Set.empty) + path
        else if !included(path) && !missing(path) then
          libs.load(path) match
            case None =>
              missing += path
              diagnostics += Diagnostic.error("E0108", s"cannot find `${imp.path}`", imp.pathSpan, "no such file")
                .withNote(s"resolved to `$path`")
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
          diagnostics += Diagnostic.error("E0108", "the prelude is missing from this installation", Span.NoSpan)
    // a program made of several files (a REPL session) is being loaded as a whole: all its files
    val rootFiles = root :: program.items.map(_.span).filter(_.exists).map(_.source.path)
    val rootImports = ImportsPhase.importsIn(program).map(i => (i, ImportsPhase.resolve(i, root)))
    visit(root, rootImports, rootFiles.distinct.map(ImportsPhase.normalize))
    ImportGraph(files.toList, cut.toMap, missing.toSet, diagnostics.toList)

/** A library file after naming (once per file, shared by all compilations): its scope, frozen, with the
 *  symbols of its declarations, their keys, and the namer's diagnostics. */
final class NamedLibrary(
    val key: NameKey,
    val parsed: Parsed,
    val scope: Scope,
    val keys: SymKeys,
    val diagnostics: List[Diagnostic]
)

/** A library file after elaboration (once per [[LibraryKey]], shared by all compilations): its body, the
 *  module value `%import` refers to, its typing results (frozen, layered over those of the prelude and of
 *  its imports), the symbol keys created by the typer, its part of the semantic index, the scopes of its
 *  module bodies and the typer's diagnostics. Compilations read these results and never change them. */
final class ElaboratedLibrary(
    val key: LibraryKey,
    val named: NamedLibrary,
    val sym: Option[Sym],
    val body: MExpr,
    val symbols: SymTable,
    val keys: SymKeys,
    val index: SemanticIndex,
    val scopes: List[(ScopeKey, Scope)],
    val diagnostics: List[Diagnostic]
)

/** Where a compilation gets its files and libraries from. The query database memoises all of these (see
 *  `hugin.query`), so the prelude and imported files are named and elaborated once and shared by every
 *  compilation that uses them; [[Libraries.direct]] computes them once per compilation. */
trait Libraries:
  /** The parsed file at a (resolved) path, or `None` if there is no such file. */
  def load(path: String): Option[Parsed]

  /** The `%import`s of a file that exists, with their resolved paths, in source order. */
  def imports(path: String): List[(Trees.Import, String)]

  /** The import graph of a program (see [[ImportGraph.compute]]). */
  def graph(root: String, program: Program, prelude: Boolean): ImportGraph

  def named(key: NameKey): NamedLibrary
  def elaborated(key: LibraryKey): ElaboratedLibrary

  /** Names the top level of the program `program` (the file `root`), see [[ProgramElab.name]]. */
  def nameProgram(root: String, source: SourceFile, program: Program, prelude: Boolean): NamedProgram =
    ProgramElab.name(root, source, program, prelude, this)

  /** Elaborates the top level of a named program, see [[ProgramElab]]. */
  def elabProgram(root: String, program: Program, prelude: Boolean, named: NamedProgram): ElaboratedProgram =
    ProgramElab.direct(root, program, prelude, named, this)

object Libraries:
  /** Computes everything from `loader`, each library once (per instance). */
  def direct(loader: SourceLoader): Libraries = new Libraries:
    private val loaded = mutable.HashMap.empty[String, Option[Parsed]]
    private val names = mutable.HashMap.empty[NameKey, NamedLibrary]
    private val elabs = mutable.HashMap.empty[LibraryKey, ElaboratedLibrary]
    def load(path: String): Option[Parsed] = loaded.getOrElseUpdate(path, loader.load(path))
    def imports(path: String): List[(Trees.Import, String)] = Library.importsOf(path, load(path).get.program)
    def graph(root: String, program: Program, prelude: Boolean): ImportGraph = ImportGraph.compute(root, program, prelude, this)
    def named(key: NameKey): NamedLibrary = names.getOrElseUpdate(key, Library.name(key, this))
    def elaborated(key: LibraryKey): ElaboratedLibrary = elabs.getOrElseUpdate(key, Library.elaborate(key, this))

/** A library file included in a compilation: the prelude or an imported file. Its items form a module
 *  body (rule M-Body) that is named, elaborated and evaluated once, however often it is imported; naming
 *  and elaboration are shared with other compilations ([[NamedLibrary]], [[ElaboratedLibrary]]), the
 *  evaluation belongs to the compilation (the object names of the prelude depend on the program). */
final class Library(val key: LibraryKey, val parsed: Parsed):
  def path: String = key.path
  def isPrelude: Boolean = key.isPrelude
  def program: Program = parsed.program

  /** Module name: the file name without extension (used for the names of its object declarations). */
  val name: String = Library.moduleName(path)

  /** The named file (filled by the namer). */
  var named: NamedLibrary | Null = null

  /** The elaborated file (filled by the typer). */
  var elaborated: ElaboratedLibrary | Null = null

  /** The scope of the file's declarations. */
  def scope: Scope | Null = if named == null then null else named.nn.scope

  /** The module value of the file; `%import` refers to it. */
  def sym: Sym | Null = if elaborated == null then null else elaborated.nn.sym.orNull

  /** The elaborated body. */
  def body: MExpr | Null = if elaborated == null then null else elaborated.nn.body

object Library:
  def moduleName(path: String): String = Path.of(path).getFileName.toString.takeWhile(_ != '.')

  /** The imports of the file `path` with their resolved paths. */
  def importsOf(path: String, program: Program): List[(Trees.Import, String)] =
    ImportsPhase.importsIn(program).map(i => (i, ImportsPhase.resolve(i, path)))

  /** An empty scope standing for a prelude that is not included (frozen, shared by all compilations). */
  val emptyPrelude: Scope =
    val sc = Scope(None, "prelude", ScopeKey.File(SourceLoader.PreludePath))
    sc.freeze()
    sc

  /** The scope enclosing the scopes of all files: the prelude's, if it is included and exists. */
  def preludeScope(prelude: Boolean, libs: Libraries): Scope =
    if prelude && libs.load(SourceLoader.PreludePath).isDefined then libs.named(NameKey(SourceLoader.PreludePath, true)).scope
    else emptyPrelude

  private def context(parsed: Parsed, prelude: Boolean, libs: Libraries): Context =
    Context(CompilationUnit(parsed.source), Settings(prelude = prelude), Reporter(), libs)

  /** Enters the declarations of a file into a new scope (frozen afterwards): the prelude's scope has no
   *  parent, every other file sees the prelude. */
  def name(key: NameKey, libs: Libraries): NamedLibrary =
    val parsed = libs.load(key.path).getOrElse(throw IllegalStateException(s"library `${key.path}` does not exist"))
    val ctx = context(parsed, key.prelude, libs)
    val scope =
      if key.isPrelude then Scope(None, "prelude", ScopeKey.File(key.path))
      else Scope(Some(preludeScope(key.prelude, libs)), s"file ${key.path}", ScopeKey.File(key.path))
    hugin.meta.Namer.enter(parsed.program.items, scope)(using ctx)
    scope.freeze()
    NamedLibrary(key, parsed, scope, ctx.unit.symKeys, ctx.reporter.diagnostics)

  /** Elaborates a named file against the prelude and the files it imports (except the imports cut by
   *  cycles, and missing ones, which denote the erroneous module); the results are frozen. */
  def elaborate(key: LibraryKey, libs: Libraries): ElaboratedLibrary =
    val named = libs.named(key.nameKey)
    val ctx = context(named.parsed, key.prelude, libs)
    val u = ctx.unit
    val prelude =
      if key.isPrelude || !key.prelude || libs.load(SourceLoader.PreludePath).isEmpty then None
      else Some(libs.elaborated(LibraryKey(SourceLoader.PreludePath, prelude = true)))
    val cut = key.cut.getOrElse(key.path, Set.empty)
    val imported =
      if key.isPrelude then Nil
      else
        libs.imports(key.path).map(_._2).distinct
          .filter(p => !cut(p) && libs.load(p).isDefined)
          .map(p => libs.elaborated(key.at(p)))
    val deps = prelude.toList ++ imported
    u.symKeys.inherit(named.keys)
    for d <- deps do
      u.symKeys.inherit(d.keys)
      val lib = Library(d.key, d.named.parsed)
      lib.named = d.named
      lib.elaborated = d
      u.libraries(d.key.path) = lib
    val typer = hugin.meta.typer.Typer(ctx, deps.map(_.symbols))
    u.symbols = typer.syms
    val program = named.parsed.program
    val (body, sig) = typer.elabBody(program.items, named.scope, program.span)
    val sym = Option.when(!key.isPrelude)(typer.moduleValue(moduleName(key.path), named.scope, sig))
    typer.syms.freeze()
    u.scopes.values.foreach(_.freeze())
    ElaboratedLibrary(key, named, sym, body, typer.syms, u.symKeys, u.index, u.scopes.toList, ctx.reporter.diagnostics)

/** Phase: load the prelude and, transitively, every imported file. */
final class ImportsPhase extends Phase:
  def phaseName = "imports"
  def description = "load the prelude and imported files; detect missing and cyclic imports"
  def run(using Context): Unit =
    val u = ctx.unit
    if u.untpd == null then return
    val graph = ctx.libraries.graph(u.source.path, u.untpd.nn, ctx.settings.prelude)
    graph.diagnostics.foreach(ctx.report)
    u.missingImports ++= graph.missing
    // only the cuts in included files matter to their elaboration (the program's own are not libraries)
    val cut = graph.cut.filter((f, _) => graph.files.contains(f))
    for path <- graph.files do
      u.libraries(path) = Library(LibraryKey(path, ctx.settings.prelude, cut).at(path), ctx.libraries.load(path).get)

object ImportsPhase:
  private[compiler] def normalize(path: String): String =
    try Path.of(path).normalize.toString
    catch case _: InvalidPathException => path

  /** The resolved path of an import: relative to the file it is written in (the source of its span), or
   *  to `from` if it has no position. */
  def resolve(imp: Trees.Import, from: String): String =
    SourceLoader.resolve(if imp.pathSpan.exists then imp.pathSpan.source.path else from, imp.path)

  /** All `%import` expressions of a program, in source order. */
  def importsIn(program: Program): List[Trees.Import] =
    val out = mutable.ListBuffer.empty[Trees.Import]
    def go(x: Any): Unit = x match
      case i: Trees.Import => out += i
      case p: Product => p.productIterator.foreach(go)
      case it: Iterable[?] => it.foreach(go)
      case _ =>
    program.items.foreach(go)
    out.toList
