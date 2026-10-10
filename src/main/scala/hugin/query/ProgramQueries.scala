package hugin.query

import hugin.compiler.{LazyStdlib, Library, ProgramElaboration, SourceLoader, StdlibCache}
import hugin.core.{ElabBase, ElaboratedDeclarations, ElaboratedItem, ProgramElab, SourceItems}
import hugin.syntax.Trees.Item
import hugin.util.*

/** The text and position of an item, for comparing items with their positions.
 *
 *  An item parsed from its own slice of the file (see [[hugin.util.SourceFile.slice]]) has item-relative
 *  spans that resolve through the slice's placement: its fingerprint is the tree, the slice (by identity)
 *  and the item's offsets in it, so it stays the same when an edit elsewhere moves the item, and results
 *  computed from it keep showing its current positions. An item that could not be parsed on its own (it
 *  has parse errors) keeps spans into the file; its fingerprint is then the tree, the file, the item's
 *  offsets, its first line and the text of all lines it touches: two items with equal fingerprints have
 *  the same spans, and every position inside them has the same line, column and line text. */
final case class ItemFingerprint(tree: Item, path: String, start: Int, end: Int, line: Int, text: String, slice: Option[SourceFile])

object ItemFingerprint:
  def of(item: Item): ItemFingerprint =
    val sp = item.span
    if !sp.exists then ItemFingerprint(item, "", 0, 0, 0, "", None)
    else if sp.origin.isSlice then ItemFingerprint(item, sp.origin.path, sp.from, sp.until, 0, "", Some(sp.origin))
    else
      val src = sp.source
      val first = src.lineOf(sp.start)
      val last = src.lineOf(sp.end)
      val to = if last + 1 < src.lineCount then src.lineStart(last + 1) else src.content.length
      ItemFingerprint(item, src.path, sp.start, sp.end, first, src.content.substring(src.lineStart(first), to), None)

/** The stable identity of an object item of a program: its file, its tree (up to positions) and which of
 *  the equal items of that file it is. Editing an item gives it a new key; other items keep theirs. */
final case class ItemKey(path: String, tree: Item, occurrence: Int)

object ItemKey:
  def assign(items: List[Item]): List[ItemKey] =
    val seen = scala.collection.mutable.HashMap.empty[(String, Item), Int]
    items.map { item =>
      val path = if item.span.exists then item.span.source.path else ""
      val k = seen.getOrElse((path, item), 0)
      seen((path, item)) = k + 1
      ItemKey(path, item, k)
    }

/** Identifies the elaboration of a program: the program (a file or a [[Composite]]) and whether the
 *  prelude is included. */
final case class ProgramKey(path: String, prelude: Boolean)

/** Identifies one object item of a program. */
final case class ItemQueryKey(program: ProgramKey, item: ItemKey)

/** A chain of library files (the prelude, then the imported files with their qualifiers, in dependency
 *  order): its last file is elaborated on top of the chain before it. */
final case class ChainKey(files: List[(String, String)], builtinNames: Boolean)

/** The prelude and the imported files, elaborated one after the other, each file once per revision of
 *  the files before it in the chain; a program's edits do not elaborate them again. */
object ElabLibrary extends Query[ChainKey, ElabBase]("elabLibrary"):
  def compute(key: ChainKey)(using db: Database): ElabBase =
    key.files match
      case Nil => ProgramElab.empty(key.builtinNames)
      // the prelude with the files it imports (they precede it), elaborated as one ([[StdlibCache]])
      case files if files.last._1 == SourceLoader.PreludePath =>
        val present = files.filter((p, _) => db.has(SourceText, p))
        if present.lastOption.exists(_._1 == SourceLoader.PreludePath) then
          StdlibCache.prelude(present.map((p, _) => db(Parse, p)), key.builtinNames)
        else ProgramElab.prelude(SourceItems(SourceLoader.PreludePath, "", Nil), key.builtinNames)
      case files =>
        val (p, q) = files.last
        ProgramElab.library(db(ElabLibrary, ChainKey(files.init, key.builtinNames)), SourceItems(p, q, items(p)))

  private def items(path: String)(using db: Database): List[Item] =
    if db.has(SourceText, path) then db(Parse, path).program.items else Nil

/** The declarations of a program ([[ProgramElab.split]]) with their fingerprints: cut off unless one of
 *  them changed (with its position), so that editing an object item does not elaborate the declarations
 *  again. */
final class ProgramDeclarations(val items: List[Item], val fingerprints: List[ItemFingerprint], val files: List[String]):
  override def equals(that: Any): Boolean = that match
    case d: ProgramDeclarations => fingerprints == d.fingerprints && files == d.files
    case _ => false
  override def hashCode: Int = fingerprints.hashCode

object DeclarationsOf extends Query[ProgramKey, ProgramDeclarations]("declarationsOf"):
  def compute(key: ProgramKey)(using db: Database): ProgramDeclarations =
    val items = db(ParseProgram, key.path).program.items
    val decls = ProgramElab.split(items)._1
    ProgramDeclarations(decls, decls.map(ItemFingerprint.of), ProgramElab.files(key.path, decls))

/** The object items of a program with their keys, in order (recomputed after every edit; cheap). Equal
 *  only if the items are, with their positions ([[ItemFingerprint]]): the items are what [[ItemOf]] reads. */
final class ObjectItems(val items: List[(ItemKey, Item)]):
  private val fingerprints = items.map((k, i) => (k, ItemFingerprint.of(i)))
  override def equals(that: Any): Boolean = that match
    case o: ObjectItems => fingerprints == o.fingerprints
    case _ => false
  override def hashCode: Int = fingerprints.hashCode

object ObjectItemsOf extends Query[ProgramKey, ObjectItems]("objectItems"):
  def compute(key: ProgramKey)(using db: Database): ObjectItems =
    val items = ProgramElab.split(db(ParseProgram, key.path).program.items)._2
    ObjectItems(ItemKey.assign(items).zip(items))

/** One item with its position ([[ItemFingerprint]]): cut off unless the item or its position changed. */
final class PositionedItem(val item: Item, val fingerprint: ItemFingerprint):
  override def equals(that: Any): Boolean = that match
    case p: PositionedItem => fingerprint == p.fingerprint
    case _ => false
  override def hashCode: Int = fingerprint.hashCode

object ItemOf extends Query[ItemQueryKey, PositionedItem]("itemOf"):
  def compute(key: ItemQueryKey)(using db: Database): PositionedItem =
    val item = db(ObjectItemsOf, key.program).items.find(_._1 == key.item).map(_._2).getOrElse(key.item.tree)
    PositionedItem(item, ItemFingerprint.of(item))

/** Whether the prelude's chain is elaborated in full, also the files it re-exports lazily
 *  ([[hugin.compiler.LazyStdlib]]): set by the language server and the REPL, whose completion offers
 *  every name in scope. */
object EagerStdlib extends Input[Unit, Boolean]("eagerStdlib"):
  override def default(key: Unit): Option[Boolean] = Some(false)

/** The files of the prelude's chain that a program elaborates, in dependency order: its import graph's,
 *  without the files the prelude re-exports lazily that the program does not use. Cut off unless they
 *  change, so that an edit of the program elaborates the chain again only if it starts or stops using
 *  such a file. */
object StdChain extends Query[ProgramKey, List[String]]("stdChain"):
  def compute(key: ProgramKey)(using db: Database): List[String] =
    val graph = db(LibraryGraph, GraphKey(key.path, key.prelude))
    graph.files.indexOf(SourceLoader.PreludePath) match
      case -1 => Nil
      case i =>
        val (std, rest) = graph.files.splitAt(i + 1)
        if db.get(EagerStdlib, ()) || !std.forall(db.has(SourceText, _)) then std
        else LazyStdlib.chain(std.map(db(Parse, _)), programFiles(key, rest), key.prelude).map(_.source.path)

/** The program's files after the prelude in its import graph (`rest`), with their parses. */
private def programFiles(key: ProgramKey, rest: List[String])(using db: Database): List[(String, hugin.syntax.Program)] =
  (key.path -> db(ParseProgram, key.path).program) :: rest.filter(db.has(SourceText, _)).map(p => p -> db(Parse, p).program)

/** The program's libraries after the prelude, in dependency order: the files after the prelude in its
 *  import graph, and the files of the prelude's chain that [[StdChain]] leaves out and the program imports
 *  ([[hugin.compiler.LazyStdlib.outside]], [[hugin.compiler.LazyStdlib.placed]]). */
object ProgramLibraries extends Query[ProgramKey, List[String]]("programLibraries"):
  def compute(key: ProgramKey)(using db: Database): List[String] =
    val graph = db(LibraryGraph, GraphKey(key.path, key.prelude))
    graph.files.indexOf(SourceLoader.PreludePath) match
      case -1 => graph.files
      case i =>
        val (std, rest) = graph.files.splitAt(i + 1)
        val chain = db(StdChain, key)
        if chain.length == std.length then rest
        else
          val parsed = std.map(db(Parse, _))
          val files = programFiles(key, rest)
          val outside = LazyStdlib.outside(parsed, parsed.filter(p => chain.contains(p.source.path)), files)
          val imports = files.toMap
          LazyStdlib.placed(outside, rest, p => imports.get(p).fold(Nil)(Library.importsOf(p, _).map(_._2)))

/** The chain of libraries a program is elaborated on: the files of its import graph. */
private def chainOf(key: ProgramKey)(using db: Database): ChainKey =
  val graph = db(LibraryGraph, GraphKey(key.path, key.prelude))
  // the prelude after its imports (an import of the prelude has no prefix), then the other files
  graph.files.indexOf(SourceLoader.PreludePath) match
    case -1 => ChainKey(Library.qualified(graph.files), key.prelude)
    case i =>
      val rest = graph.files.drop(i + 1)
      ChainKey(db(StdChain, key).map(_ -> "") ++ Library.qualified(db(ProgramLibraries, key)), key.prelude)

/** The declarations of a program, elaborated on its libraries. */
object Signatures extends Query[ProgramKey, ElaboratedDeclarations]("signatures"):
  def compute(key: ProgramKey)(using db: Database): ElaboratedDeclarations =
    val decls = db(DeclarationsOf, key)
    val base = db(ElabLibrary, chainOf(key))
    ProgramElab.declarations(base, key.path, decls.files, decls.items)

/** One object item of a program, elaborated against the program's declarations: recomputed only when the
 *  item (with its position) or the declarations change. */
object ElabItem extends Query[ItemQueryKey, ElaboratedItem]("elabItem"):
  def compute(key: ItemQueryKey)(using db: Database): ElaboratedItem =
    ProgramElab.item(db(Signatures, key.program), db(ItemOf, key).item)

/** A program assembled from its elaborated parts (recomputed after every edit of the program; the parts
 *  are reused). */
object ElabProgram extends Query[ProgramKey, ProgramElaboration]("elabFile"):
  def compute(key: ProgramKey)(using db: Database): ProgramElaboration =
    val decls = db(Signatures, key)
    val items = db(ObjectItemsOf, key).items.map((k, _) => db(ElabItem, ItemQueryKey(key, k)))
    val (elaborated, diagnostics, index) = ProgramElab.assemble(decls, items)
    ProgramElaboration(elaborated, diagnostics, index)
