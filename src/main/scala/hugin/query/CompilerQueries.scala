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

/** Parses the slice of one top-level item of a file on its own ([[hugin.syntax.Slices]]), keyed by its
 *  text: an item whose text did not change is the same tree, with the same item-relative spans, after any
 *  edit elsewhere in the file. It reads nothing, so it is computed once per key. */
object ParseItem extends Query[hugin.syntax.Slices.Key, hugin.syntax.Slices.Parsed]("parseItem"):
  def compute(key: hugin.syntax.Slices.Key)(using db: Database): hugin.syntax.Slices.Parsed = hugin.syntax.Slices.parse(key)

/** A file as the program of a compilation: the whole file parsed (which decides where its items are, and
 *  reports parse diagnostics) and its top-level items, parsed from their slices where possible. */
final class SlicedFile(val parsed: Parsed, val items: List[hugin.syntax.Trees.Item])

/** Splits a file into its items' slices ([[hugin.syntax.Slices]]) and places the slices at their offsets
 *  in the current text of the file: the boundary between item-relative and file positions (`ItemOffsets`
 *  in `docs/INCREMENTALITY.md`). Recomputed after every edit of the file, before anything reads positions
 *  of its items (every query on a program's items depends on it through [[ParseProgram]]). */
object ItemSlices extends Query[String, SlicedFile]("itemSlices"):
  def compute(path: String)(using db: Database): SlicedFile =
    val parsed = db(Parse, path)
    SlicedFile(parsed, hugin.syntax.Slices.items(parsed.source, parsed.program, k => db(ParseItem, k)))

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

  // the program being compiled is named and elaborated by queries (per item); another program directly
  private def isProgram(root: String, program: hugin.syntax.Program): Boolean = db(ParseProgram, root).program eq program
  override def nameProgram(root: String, source: SourceFile, program: hugin.syntax.Program, prelude: Boolean): NamedProgram =
    if isProgram(root, program) then db(ScopeOf, ProgramKey(root, prelude)) else super.nameProgram(root, source, program, prelude)
  override def elabProgram(root: String, program: hugin.syntax.Program, prelude: Boolean, named: NamedProgram): ElaboratedProgram =
    if isProgram(root, program) then db(ElabFile, ProgramKey(root, prelude)) else super.elabProgram(root, program, prelude, named)

/** A file of a program made of several files ([[Composite]]); its queries are left out unless `queries`. */
final case class Part(path: String, queries: Boolean = true)

/** The files of a program that is not one file, such as a REPL session (its inputs and loaded files): the
 *  items of the parts, in order, form one module body. A path without this input is a file of its own. */
object Composite extends Input[String, Vector[Part]]("composite")

/** Parses a program: the file at `path`, or the parts set as its [[Composite]]. The items of a part keep
 *  their own source file, so their diagnostics point into it and their `%import`s resolve relative to it.
 *  Items are parsed from their slices ([[ItemSlices]]), so their spans are item-relative. */
object ParseProgram extends Query[String, Parsed]("parseProgram"):
  def compute(path: String)(using db: Database): Parsed =
    if !db.has(Composite, path) then
      val sliced = db(ItemSlices, path)
      sliced.parsed.copy(program = hugin.syntax.Program(sliced.items, sliced.parsed.program.span))
    else
      val parts = db.get(Composite, path).map(p => (p, db(ItemSlices, p.path)))
      val items = parts.toList.flatMap((p, sliced) =>
        if p.queries then sliced.items else sliced.items.filterNot(_.isInstanceOf[hugin.syntax.Trees.Query])
      )
      Parsed(SourceFile.virtual(path, ""), hugin.syntax.Program(items, Span.NoSpan), parts.toList.flatMap(_._2.parsed.diagnostics))

// ------------------------------------------------------------------------------ per-item elaboration

/** Identifies the elaboration of a program's top level: the program (a file or a [[Composite]]) and
 *  whether the prelude is included (the only option the typer reads). */
final case class ProgramKey(path: String, prelude: Boolean)

/** Identifies one top-level item of a program by its stable key (see [[hugin.meta.ItemKey]]). */
final case class ItemQueryKey(program: ProgramKey, item: hugin.meta.ItemKey)

/** Diagnostics of the program's naming and elaboration, accumulated by the queries that compute them. */
object ProgramDiagnostics extends Accumulator[Diagnostic]("programDiagnostics")

/** The top-level items of a program with their keys, in order, and the declarations after each item.
 *  Recomputed after every edit of the program (cheap); the per-item queries project it. */
final class ProgramItems(val items: List[(hugin.meta.ItemKey, hugin.syntax.Trees.Item)]):
  val byKey: Map[hugin.meta.ItemKey, hugin.syntax.Trees.Item] = items.toMap
  lazy val later: Map[hugin.meta.ItemKey, List[hugin.meta.ItemKey]] = ProgramElab.laterDeclarations(items)
  lazy val laterSet: Map[hugin.meta.ItemKey, Set[hugin.meta.ItemKey]] = later.view.mapValues(_.toSet).toMap

object ProgramItemsOf extends Query[ProgramKey, ProgramItems]("programItems"):
  def compute(key: ProgramKey)(using db: Database): ProgramItems =
    val items = db(ParseProgram, key.path).program.items
    ProgramItems(items.zip(hugin.meta.ItemKey.assign(hugin.meta.ScopeKey.File(key.path), items)).map(_.swap))

/** One item with its position ([[ItemFingerprint]]): cut off unless the item or its position changed; the
 *  position of an item parsed from its slice is item-relative, so moving the item does not change it. */
final class PositionedItem(val item: hugin.syntax.Trees.Item, val fingerprint: ItemFingerprint):
  override def equals(that: Any): Boolean = that match
    case p: PositionedItem => fingerprint == p.fingerprint
    case _ => false
  override def hashCode: Int = fingerprint.hashCode

object ItemOf extends Query[ItemQueryKey, PositionedItem]("itemOf"):
  def compute(key: ItemQueryKey)(using db: Database): PositionedItem =
    val item = db(ProgramItemsOf, key.program).byKey(key.item)
    PositionedItem(item, ItemFingerprint.of(item))

final case class OrderKey(item: ItemQueryKey, decl: hugin.meta.ItemKey)

/** Whether a declaration or definition comes after an item: its meta definitions and formula functions
 *  are hidden from the item (E0105). An item depends on this for the declarations it asked about, not on
 *  all declarations after it, so adding a declaration (such as a new input of a REPL session) does not
 *  elaborate the items before it again. */
object DeclAfter extends Query[OrderKey, Boolean]("declAfter"):
  def compute(key: OrderKey)(using db: Database): Boolean =
    db(ProgramItemsOf, key.item.program).laterSet.getOrElse(key.item.item, Set.empty).contains(key.decl)

/** Names the top level of a program ([[NamedProgram]]); cut off unless a declaration, a clause or a
 *  `%mode` of a formula function changed (with its position), or the prelude did. */
object ScopeOf extends Query[ProgramKey, NamedProgram]("scopeOf"):
  def compute(key: ProgramKey)(using db: Database): NamedProgram =
    val parsed = db(ParseProgram, key.path)
    val named = ProgramElab.name(key.path, parsed.source, parsed.program, key.prelude, DatabaseLibraries())
    named.diagnostics.foreach(db.push(ProgramDiagnostics, _))
    named

/** The names declared at a program's top level with their kinds and keys, and the enclosing scope: what
 *  an item depends on when it lists all names (for the suggestion of a similar name). */
final class ScopeNamesValue(val names: List[(String, hugin.meta.SymKind, hugin.meta.SymKey)], val parent: Option[hugin.meta.Scope]):
  override def equals(that: Any): Boolean = that match
    case n: ScopeNamesValue => names == n.names && parent.zip(n.parent).forall(_ eq _) && parent.isDefined == n.parent.isDefined
    case _ => false
  override def hashCode: Int = names.hashCode

object ScopeNames extends Query[ProgramKey, ScopeNamesValue]("scopeNames"):
  def compute(key: ProgramKey)(using db: Database): ScopeNamesValue =
    val scope = db(ScopeOf, key).scope
    ScopeNamesValue(scope.decls.values.toList.map(s => (s.name, s.kind, s.key)), scope.parent)

final case class ScopeNameKey(program: ProgramKey, name: String)

/** What one name denotes at a program's top level (the kind and key of its symbol, or nothing, so that a
 *  lookup falls through to the enclosing scope), and the enclosing scope: what name resolution in an
 *  item depends on for each name it looks up, besides the declaration it finds ([[DeclSig]]). */
final class ScopeNameValue(val sym: Option[(hugin.meta.SymKind, hugin.meta.SymKey)], val parent: Option[hugin.meta.Scope]):
  override def equals(that: Any): Boolean = that match
    case n: ScopeNameValue => sym == n.sym && parent.zip(n.parent).forall(_ eq _) && parent.isDefined == n.parent.isDefined
    case _ => false
  override def hashCode: Int = sym.hashCode

object ScopeName extends Query[ScopeNameKey, ScopeNameValue]("scopeName"):
  def compute(key: ScopeNameKey)(using db: Database): ScopeNameValue =
    val scope = db(ScopeOf, key.program).scope
    ScopeNameValue(scope.decls.get(key.name).map(s => (s.kind, s.key)), scope.parent)

/** The libraries of a program, elaborated (cut off unless one of them changed). */
object ProgramLibrariesOf extends Query[ProgramKey, ProgramLibraries]("programLibraries"):
  def compute(key: ProgramKey)(using db: Database): ProgramLibraries =
    ProgramElab.libraries(key.path, db(ParseProgram, key.path).program, key.prelude, DatabaseLibraries())

/** The declarations and definitions of a program, elaborated together ([[ProgramSignatures]]): recomputed
 *  when one of them changes; the items depend on its parts ([[DeclSig]]), not on it. */
object Signatures extends Query[ProgramKey, ProgramSignatures]("signatures"):
  def compute(key: ProgramKey)(using db: Database): ProgramSignatures =
    val named = db(ScopeOf, key)
    val sigs = ProgramElab.signatures(named, db(ProgramLibrariesOf, key), key.prelude, DatabaseLibraries())
    sigs.diagnostics.foreach(db.push(ProgramDiagnostics, _))
    sigs

final case class DeclSigKey(program: ProgramKey, owner: SigOwner)

/** What items see of one declaration ([[DeclSigValue]]: an object declaration's columns, a type
 *  definition, a meta definition's type and value, with the positions of the declaring item); cut off
 *  unless that changed, so that only the items using a declaration are elaborated again after it changed. */
object DeclSig extends Query[DeclSigKey, DeclSigValue]("declSig"):
  def compute(key: DeclSigKey)(using db: Database): DeclSigValue =
    db(Signatures, key.program).parts.getOrElse(key.owner, DeclSigValue.empty)

/** Elaborates one top-level item of a program that is not a declaration or definition (a rule, query,
 *  directive or subtyping edge). It depends on the item with its position, on the libraries, and on what
 *  it read of the top level: each name it looked up ([[ScopeName]], or all names, [[ScopeNames]]), the
 *  order of the declarations whose meta definitions it asked about ([[DeclAfter]]) and the parts of the
 *  signatures it read ([[DeclSig]]). The shared results it is elaborated against (the scope, the
 *  signatures, the items of the program) are read untracked, since those dependencies cover everything
 *  it uses of them; so an edit elsewhere, also adding a declaration, does not elaborate it again unless it
 *  changes a name the item uses. */
object ElabItem extends Query[ItemQueryKey, ElaboratedItem]("elabItem"):
  def compute(key: ItemQueryKey)(using db: Database): ElaboratedItem =
    val item = db(ItemOf, key).item
    val plibs = db(ProgramLibrariesOf, key.program)
    val later = db.untracked(ProgramItemsOf, key.program).laterSet.getOrElse(key.item, Set.empty)
    val named = db.untracked(ScopeOf, key.program)
    val sigs = db.untracked(Signatures, key.program)
    val (elaborated, reads) =
      ProgramElab.item(named, sigs, plibs, key.item, item, later, key.program.prelude, DatabaseLibraries())
    if reads.listed then db(ScopeNames, key.program)
    reads.names.foreach(n => db(ScopeName, ScopeNameKey(key.program, n)))
    reads.ordered.foreach(d => db(DeclAfter, OrderKey(key, d)))
    reads.owners.foreach(o => db(DeclSig, DeclSigKey(key.program, o)))
    elaborated.diagnostics.foreach(db.push(ProgramDiagnostics, _))
    elaborated

/** The top level of a program, elaborated: its parts assembled in item order (recomputed after every edit
 *  of the program; the parts are reused). */
object ElabFile extends Query[ProgramKey, ElaboratedProgram]("elabFile"):
  def compute(key: ProgramKey)(using db: Database): ElaboratedProgram =
    val program = db(ParseProgram, key.path).program
    val named = db(ScopeOf, key)
    val sigs = db(Signatures, key)
    val items = db(ProgramItemsOf, key).items
    ProgramElab.assemble(named, sigs, items, k => db(ElabItem, ItemQueryKey(key, k)), program.span)

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
    // the new meta level has its own syntax; it is parsed as a whole file (no per-item incrementality yet)
    val parsed = if key.settings.newMeta then Parsed.meta2(db(Parse, key.path).source) else db(ParseProgram, key.path)
    val ctx = Compiler.compileWith(parsed, key.settings, DatabaseLibraries(), printed += _)
    Compiled(ctx, printed.toList)

final case class EvaluateKey(compile: CompileKey, facts: List[String] = Nil, allRelations: Boolean = false)

/** Evaluates a compiled program over input facts. Changing only a facts file re-evaluates without
 *  recompiling; an evaluation with an unchanged outcome does not invalidate its dependents. */
object Evaluate extends Query[EvaluateKey, Evaluation.Outcome]("evaluate"):
  def compute(key: EvaluateKey)(using db: Database): Evaluation.Outcome =
    val compiled = db(Compile, key.compile)
    val facts = key.facts.map(f => SourceFile.virtual(f, db.get(SourceText, f)))
    Evaluation.run(compiled.context, facts, key.allRelations)
