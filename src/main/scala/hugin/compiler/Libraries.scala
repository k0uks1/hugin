package hugin.compiler

import hugin.meta.{MExpr, Scope, Sym}
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

  /** Resolves an import path relative to the importing file; `.hgn` is appended if there is no extension. */
  def resolve(from: String, path: String): String =
    val withExt = if Path.of(path).getFileName.toString.contains('.') then path else path + ".hgn"
    val parent = Option(Path.of(from).getParent)
    parent.map(_.resolve(withExt)).getOrElse(Path.of(withExt)).normalize.toString

/** A source file included in a compilation: the prelude or an imported file. Its items form a module
 *  body (rule M-Body) that is elaborated and evaluated once, however often it is imported. */
final class Library(val path: String, val parsed: Parsed, val isPrelude: Boolean):
  def program: Program = parsed.program

  /** Module name: the file name without extension (used for the names of its object declarations). */
  val name: String = Path.of(path).getFileName.toString.takeWhile(_ != '.')

  /** The scope of the file's declarations (filled by the namer). */
  var scope: Scope | Null = null

  /** The module value of the file (filled by the typer); `%import` refers to it. */
  var sym: Sym | Null = null

  /** The elaborated body (filled by the typer). */
  var body: MExpr | Null = null

/** Phase: load the prelude and, transitively, every imported file. */
final class ImportsPhase extends Phase:
  def phaseName = "imports"
  def description = "load the prelude and imported files; detect missing and cyclic imports"
  def run(using Context): Unit =
    val u = ctx.unit
    if u.untpd == null then return
    if ctx.settings.prelude then
      ctx.loader.load(SourceLoader.PreludePath) match
        case Some(p) =>
          p.diagnostics.foreach(ctx.report)
          visit(SourceLoader.PreludePath, p.program, List(SourceLoader.PreludePath))
          u.libraries(SourceLoader.PreludePath) = Library(SourceLoader.PreludePath, p, isPrelude = true)
        case None =>
          ctx.report(Diagnostic.error("E0108", "the prelude is missing from this installation", Span.NoSpan))
    val self = Path.of(u.source.path).normalize.toString
    visit(u.source.path, u.untpd.nn, List(self))

  /** Loads the imports of `program` (in the file `from`); `stack` lists the files being loaded. Libraries
   *  are added after their own imports, so `libraries` is in dependency order. */
  private def visit(from: String, program: Program, stack: List[String])(using Context): Unit =
    val u = ctx.unit
    for imp <- ImportsPhase.importsIn(program) do
      val path = SourceLoader.resolve(from, imp.path)
      u.imports.put(imp, path)
      if stack.contains(path) then
        val cycle = (path :: stack.takeWhile(_ != path).reverse) :+ path
        ctx.report(
          Diagnostic.error("E0108", s"cyclic import of `${imp.path}`", imp.pathSpan, "imported here")
            .withNote(s"import cycle: ${cycle.mkString(" -> ")}")
            .withHelp("a file is a module body; move what both files need into a third file")
        )
      else if !u.libraries.contains(path) && !u.missingImports(path) then
        ctx.loader.load(path) match
          case None =>
            u.missingImports += path
            ctx.report(
              Diagnostic.error("E0108", s"cannot find `${imp.path}`", imp.pathSpan, "no such file")
                .withNote(s"resolved to `$path`")
            )
          case Some(p) =>
            p.diagnostics.foreach(ctx.report)
            visit(path, p.program, path :: stack)
            if !u.libraries.contains(path) then u.libraries(path) = Library(path, p, isPrelude = false)

object ImportsPhase:
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
