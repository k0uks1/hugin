package hugin.core

import hugin.syntax.Trees.{Decl, Def, Item}
import hugin.util.*

/** A program elaborated by the new meta level: the core state, the elaborated items of all its files (the
 *  prelude, the imported files, the program) and those of the program itself. */
final class Elaborated(val core: Core, val items: List[CoreItem], val programItems: List[CoreItem]):
  /** The elaborated program: definitions (with the inserted quotes, splices and implicit arguments) and
   *  the staged object items (for `--print-after elaborate`). */
  def render(reporter: Reporter): List[String] = Staging(core, reporter).render(programItems)

/** A source file of a program: its path, the qualifier of its object constants, its items. */
final case class SourceItems(path: String, qualifier: String, items: List[Item])

/** Entry point of the new meta level: elaborates the files of a program into one core, in dependency
 *  order. The prelude's names are in scope in every other file; an imported file is the module value of
 *  its `%import`s ([[elab.Imports]]). */
object NewMeta:
  def elaborate(
      program: SourceItems,
      prelude: Option[SourceItems],
      libraries: List[SourceItems],
      reporter: Reporter,
      builtinNames: Boolean = true
  ): Elaborated =
    val core = Core()
    (prelude.toList ++ libraries).map(_.qualifier).foreach(core.reservePrefix)
    val shadowed = program.items.flatMap(declared).toSet
    val preludeElab = prelude.map(p => elabFile(core, reporter, p, elab.FileEnv(p.path, p.qualifier, shadowed)))
    val parent = preludeElab.fold(Map.empty[Name, Int])(_.scope.toMap)
    var imports = Map.empty[String, elab.ImportedModule]
    val libElabs = libraries.map { lib =>
      val e = elabFile(core, reporter, lib, elab.FileEnv(lib.path, lib.qualifier, Set.empty, parent, imports, builtinNames = builtinNames))
      imports += lib.path -> e.moduleValue
      e
    }
    val main =
      elabFile(core, reporter, program, elab.FileEnv(program.path, program.qualifier, Set.empty, parent, imports, true, builtinNames))
    val all = (preludeElab.toList ++ libElabs :+ main).flatMap(_.items.toList)
    Elaborated(core, all, main.items.toList)

  private def elabFile(core: Core, reporter: Reporter, file: SourceItems, env: elab.FileEnv): elab.Elaborator =
    val e = elab.Elaborator(core, reporter, env)
    e.elabProgram(file.items)
    e

  private def declared(item: Item): Option[Name] = item match
    case d: Decl => Some(d.name.name)
    case d: Def => Some(d.name.name)
    case _ => None

  /** Elaborates a single file without prelude and imports. */
  def elaborateFile(path: String, items: List[Item], reporter: Reporter): Elaborated =
    elaborate(SourceItems(path, "", items), None, Nil, reporter)

  /** The diagnostics of parsing a file in the new syntax, elaborating it and staging its object items
   *  (without the object-level phases). */
  def check(src: SourceFile): List[Diagnostic] =
    val reporter = Reporter()
    val prog = hugin.syntax.Parser.parseMeta2(src, reporter)
    if !reporter.hasErrors then
      val e = elaborateFile(src.path, prog.items, reporter)
      if !reporter.hasErrors then e.render(reporter)
    reporter.sorted
