package hugin.ide

import hugin.query.{CompileKey, Database, Ide}
import hugin.util.Span

/** Where a name is declared. */
enum Target:
  /** A declaration in a source file: the program's or one it imports (for an object variable, its first
   *  occurrence in the rule). */
  case InFile(span: Span)

  /** A declaration `name` of the bundled standard library's module `module` (`prelude`, `std/graph`),
   *  which has no file an editor could open. */
  case Library(module: String, name: String)

/** Go to definition and find references. */
object Navigation:
  /** The declaration of the name at an offset of the program `key`. */
  def definition(key: CompileKey, offset: Int)(using Database): Option[Target] =
    if Files.isFacts(key.path) then None else Ide.definition(key, offset).map(target(key, offset, _))

  private def target(key: CompileKey, offset: Int, decl: Span)(using Database): Target =
    if Files.isLibrary(decl.source.path) then
      Target.Library(Files.libraryModule(decl.source.path), Ide.symbolAt(key, offset).fold(decl.text)(_.name))
    else Target.InFile(decl)

  /** The occurrences of the name at an offset, in source order: its uses, and its declaration if
   *  `includeDeclaration`. Declarations in the bundled standard library are included; an editor that
   *  cannot open them leaves them out. */
  def references(key: CompileKey, offset: Int, includeDeclaration: Boolean)(using Database): List[Span] =
    if Files.isFacts(key.path) then Nil
    else
      val decl = Ide.definition(key, offset)
      Ide.references(key, offset).filter(sp => includeDeclaration || !decl.contains(sp))
