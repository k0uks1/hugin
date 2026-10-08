package hugin.core
package elab

import hugin.syntax.Trees.Import

/** Imports (REDESIGN §6.7, docs/LIBRARIES.md): `%import "f"` is the module value of the file `f`, a
 *  record of its declarations, elaborated once per compilation (so every import of a file denotes the
 *  same object constants). Its type is the record type of the declarations' types; since they refer to
 *  the file's constants themselves, ascribing a signature (`s : sig = %import "f".`) is transparent. A
 *  file that is missing or closes a cycle (reported as E0108 by the import graph) is the empty module. */
trait Imports:
  self: Elaborator =>
  import core.*

  def inferImport(imp: Import): (Tm, Val, Stage) =
    val path = hugin.compiler.ImportPaths.resolve(imp, file.path)
    file.imports.get(path) match
      case Some(m) => (m.value, eval(Nil, m.ty), Stage.S1)
      case None => erroneous(imp.span)

  /** A missing or cyclic import was reported (E0108); the item using it, and the items using what it
   *  defines, are dropped without further errors. */
  private def erroneous(span: hugin.util.Span): Nothing =
    throw ElabError(ElabProblem.UnresolvedName("%import", span, None, false).toDiagnostic, silent = true)

  /** The module value of the file elaborated by this elaborator: its declarations in order. */
  def moduleValue: ImportedModule =
    val fields = scope.toList.flatMap((n, id) => field(id).map((n, _)))
    val decls = scope.toList.filter((_, id) => field(id).isDefined).map((_, id) => (globals(id).span, globals(id).declSpan))
    ImportedModule(Tm.Rec(fields.map((n, f) => (n, f._1))), Tm.RecTy(fields.map((n, f) => (n, f._2)), Nil, decls), state.erroneous.toSet)

  /** Whether `m.l` names a declaration of an imported file that was dropped for an error there. */
  def droppedImport(qual: hugin.syntax.Tree, label: Name): Boolean = qual match
    case hugin.syntax.Trees.Ident(n) =>
      scope.get(n).orElse(file.parent.get(n)).map(globals(_).kind).exists {
        case GlobalKind.Definition(tm, _) => file.imports.values.exists(m => m.value == tm && m.dropped(label))
        case _ => false
      }
    case _ => false

  /** A declaration as a field: an object constant is object code (`⟨c⟩ : ⇑τ`), anything else itself. */
  private def field(id: Int): Option[(Tm, Tm)] =
    val g = globals(id)
    if g.pending then None
    else
      g.kind match
        case GlobalKind.Object(_) => Some((Tm.Quote(Tm.Global(id)), Tm.Lift(g.tyTm)))
        case _ => Some((Tm.Global(id), g.tyTm))
