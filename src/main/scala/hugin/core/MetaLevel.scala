package hugin.core

import hugin.syntax.Trees.Item
import hugin.util.*

/** A program elaborated by the meta level: the core state, the elaborated items of all its files (the
 *  prelude, the imported files, the program) and those of the program itself. */
final class Elaborated(val core: Core, val items: List[CoreItem], val programItems: List[CoreItem]):
  /** The elaborated program: definitions (with the inserted quotes, splices and implicit arguments) and
   *  the staged object items (for `--print-after elaborate`). */
  def render(reporter: Reporter): List[String] = Staging(core, reporter).render(programItems)

/** A source file of a program: its path, the qualifier of its object constants, its items. */
final case class SourceItems(path: String, qualifier: String, items: List[Item])

/** Entry point of the meta level: elaborates the files of a program into one core, in dependency
 *  order, in the parts of [[ProgramElab]]. The prelude's names are in scope in every other file; an
 *  imported file is the module value of its `%import`s ([[elab.Imports]]). */
object MetaLevel:
  def elaborate(
      program: SourceItems,
      prelude: Option[SourceItems],
      libraries: List[SourceItems],
      reporter: Reporter,
      builtinNames: Boolean = true,
      index: hugin.compiler.SemanticIndex = hugin.compiler.SemanticIndex()
  ): Elaborated =
    val base0 = prelude.fold(ProgramElab.empty(builtinNames))(ProgramElab.prelude(_, builtinNames))
    // (a prelude given here has no imports: the core tests' preludes declare everything themselves)
    elaborateOn(base0, program, libraries, reporter, index)

  /** Elaborates `program` with the imported files `libraries` on the prelude's (or an empty) base. */
  private def elaborateOn(
      base0: ElabBase,
      program: SourceItems,
      libraries: List[SourceItems],
      reporter: Reporter,
      index: hugin.compiler.SemanticIndex
  ): Elaborated =
    val base = libraries.foldLeft(base0)(ProgramElab.library)
    val (decls, objectItems) = ProgramElab.split(program.items)
    val declarations = ProgramElab.declarations(base, program.path, ProgramElab.files(program.path, decls), decls)
    val (elaborated, diagnostics, idx) = ProgramElab.assemble(declarations, objectItems.map(ProgramElab.item(declarations, _)))
    diagnostics.foreach(reporter.report)
    index.include(idx)
    elaborated

  /** Elaborates the program `program` (the file `root`) with the files of its import graph, read with
   *  `load`. The prelude comes from [[hugin.compiler.StdlibCache]]. */
  def elaborateProgram(
      root: String,
      program: hugin.syntax.Program,
      graph: hugin.compiler.ImportGraph,
      prelude: Boolean,
      load: String => Option[hugin.compiler.Parsed]
  ): hugin.compiler.ProgramElaboration =
    val reporter = Reporter()
    val index = hugin.compiler.SemanticIndex()
    def items(path: String) = load(path).fold(Nil)(_.program.items)
    // the prelude comes after the files it imports, which precede every other file in the graph
    val (std, rest) = graph.files.indexOf(hugin.compiler.SourceLoader.PreludePath) match
      case -1 => (Nil, graph.files)
      case i => (graph.files.take(i + 1), graph.files.drop(i + 1))
    val base0 =
      if std.isEmpty then ProgramElab.empty(prelude)
      else
        // the files the prelude re-exports lazily are left out unless the program may use them
        val others = (root -> program) :: rest.flatMap(p => load(p).map(p -> _.program))
        hugin.compiler.StdlibCache.prelude(hugin.compiler.LazyStdlib.chain(std.flatMap(load), others, prelude), prelude)
    val libraries = hugin.compiler.Library.qualified(rest).map((p, q) => SourceItems(p, q, items(p)))
    val e = elaborateOn(base0, SourceItems(root, "", program.items), libraries, reporter, index)
    hugin.compiler.ProgramElaboration(e, reporter.diagnostics, index)

  /** Elaborates a single file without prelude and imports. */
  def elaborateFile(path: String, items: List[Item], reporter: Reporter): Elaborated =
    elaborate(SourceItems(path, "", items), None, Nil, reporter)

  /** The diagnostics of parsing a file in the new syntax, elaborating it and staging its object items
   *  (without the object-level phases). */
  def check(src: SourceFile): List[Diagnostic] =
    val reporter = Reporter()
    val prog = hugin.syntax.Parser.parse(src, reporter)
    if !reporter.hasErrors then
      val e = elaborateFile(src.path, prog.items, reporter)
      if !reporter.hasErrors then e.render(reporter)
    reporter.sorted
