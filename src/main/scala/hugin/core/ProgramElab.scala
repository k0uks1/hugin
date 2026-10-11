package hugin.core

import hugin.compiler.SemanticIndex
import hugin.syntax.Trees.Item
import hugin.util.*
import scala.collection.mutable

/** What the files elaborated so far provide to the next: their core (later parts fork it, so it is never
 *  changed again), the prelude's names, the module values of the imported files, their elaborated items,
 *  diagnostics and tooling index. */
final class ElabBase(
    val core: Core,
    val prelude: Map[Name, Int],
    val imports: Map[String, elab.ImportedModule],
    val items: List[CoreItem],
    val diagnostics: List[Diagnostic],
    val index: SemanticIndex,
    val builtinNames: Boolean
)

/** A program's declarations ([[elab.Items.splitItems]]) elaborated against a base: the elaborator (its core
 *  and its state are the declarations' and are only forked from), its items, diagnostics and index. */
final class ElaboratedDeclarations(
    val base: ElabBase,
    val elaborator: elab.Elaborator,
    val items: List[CoreItem],
    val diagnostics: List[Diagnostic],
    val index: SemanticIndex
):
  def core: Core = elaborator.core

  /** What object items can read of these declarations, comparable across their elaborations. */
  lazy val summary: DeclarationsSummary = DeclarationsSummary(this)

/** One object item of a program (a rule, query or directive) elaborated on its own against the program's
 *  declarations, in a fork of their core: its items, diagnostics, index and the globals it used. It is
 *  *portable* if its items can be moved into another fork of the declarations' core: the only globals
 *  it created are family instances (recreated there) and it created no module instance or universe
 *  level of its own; otherwise the item is elaborated again where the program is assembled. */
final class ElaboratedItem(
    val item: Item,
    val fork: Core,
    val items: List[CoreItem],
    val diagnostics: List[Diagnostic],
    val index: SemanticIndex,
    val used: Set[Int],
    val portable: Boolean,
    /** What the item contributes to the module that module-wide directives rewrite. */
    val parts: List[elab.ModulePart] = Nil,
    /** What it read of the declarations ([[Footprint]]). */
    val footprint: Footprint | Null = null,
    /** The declarations it was elaborated against (assembly may move it onto later ones, [[Rebase]]). */
    val declarations: ElaboratedDeclarations | Null = null
)

/** The elaboration of a program in parts, each a function of the parts before it, so that a query
 *  database can memoise them (`hugin.query`): the prelude and the imported files one after the other
 *  ([[prelude]], [[library]]); the program's declarations ([[declarations]]); each object item on its own
 *  against them ([[item]]); and the program assembled from these ([[assemble]]). Every part forks the
 *  core of the part before it, so the parts can be reused and recombined: an edit of a rule elaborates
 *  that rule again, nothing else. [[MetaLevel.elaborate]] runs the parts in sequence.
 *
 *  An item elaborated on its own sees exactly what it sees when the items are elaborated together: the
 *  declarations, and no other object item (object items do not declare anything). */
object ProgramElab:
  /** The base of a program without prelude and imports. */
  def empty(builtinNames: Boolean): ElabBase =
    ElabBase(Core(), Map.empty, Map.empty, Nil, Nil, SemanticIndex(), builtinNames)

  /** The prelude without imports, elaborated into a new core: its names are in scope in every other file. */
  def prelude(file: SourceItems, builtinNames: Boolean): ElabBase = preludeOn(empty(builtinNames), file)

  /** The prelude after the files it imports (`libraries`, in dependency order, which see no prelude):
   *  the standard library's chain (reference: prelude). */
  def preludeChain(libraries: List[SourceItems], prelude: SourceItems, builtinNames: Boolean): ElabBase =
    preludeOn(libraries.foldLeft(empty(builtinNames))(library), prelude)

  /** The prelude, elaborated in a fork of `base` (its imports): its names, and the names it opens with
   *  `%use`, are in scope in every later file. */
  def preludeOn(base: ElabBase, file: SourceItems): ElabBase =
    val core = base.core.fork()
    val env = elab.FileEnv(file.path, file.qualifier, Map.empty, base.imports, builtinNames = base.builtinNames)
    val (e, diagnostics) = elabFile(core, file, env)
    val index = SemanticIndex()
    index.include(base.index)
    index.include(e.index)
    // the names it opens are in scope in every file too, unless it declares them itself
    val opened = e.state.opened.collect { case (n, List((id, _))) if !e.state.declaredHere(n) => n -> id }
    ElabBase(core, opened ++ e.scope.toMap, base.imports, base.items ++ e.items, base.diagnostics ++ diagnostics, index, base.builtinNames)

  /** An imported file, elaborated in a fork of `base`: its module value is what `%import` denotes. */
  def library(base: ElabBase, file: SourceItems): ElabBase =
    val core = base.core.fork()
    core.reservePrefix(file.qualifier)
    val env = elab.FileEnv(file.path, file.qualifier, base.prelude, base.imports, builtinNames = base.builtinNames)
    val (e, diagnostics) = elabFile(core, file, env)
    val index = SemanticIndex()
    index.include(base.index)
    index.include(e.index)
    val imports = base.imports + (file.path -> e.moduleValue)
    ElabBase(core, base.prelude, imports, base.items ++ e.items, base.diagnostics ++ diagnostics, index, base.builtinNames)

  /** The declarations of an imported file without the clauses of its functions, elaborated in a fork of
   *  `base`: their kinds and types ([[elab.FileEnv.signaturesOnly]]). */
  def signatures(base: ElabBase, file: SourceItems): ElabBase =
    val core = base.core.fork()
    val env = elab.FileEnv(file.path, file.qualifier, base.prelude, base.imports, builtinNames = base.builtinNames, signaturesOnly = true)
    val (e, diagnostics) = elabFile(core, file, env)
    ElabBase(core, base.prelude, base.imports, base.items ++ e.items, base.diagnostics ++ diagnostics, base.index, base.builtinNames)

  private def elabFile(core: Core, file: SourceItems, env: elab.FileEnv): (elab.Elaborator, List[Diagnostic]) =
    core.rankFile(file.path)
    val reporter = Reporter()
    val e = elab.Elaborator(core, reporter, env, SemanticIndex())
    e.elabProgram(file.items)
    (e, reporter.diagnostics)

  /** The declarations and the object items of a program, in source order. */
  def split(items: List[Item]): (List[Item], List[Item]) = elab.Elaborator(Core(), Reporter()).splitItems(items)

  /** The files of a program's items, in order (a program of several files: a REPL session), after the
   *  program's path: the order in which they are placed in the object program. */
  def files(path: String, items: List[Item]): List[String] =
    (path :: items.map(_.span).filter(_.exists).map(_.source.path)).distinct

  /** The declarations `decls` of the program at `path` (made of the files `files`), elaborated in a fork
   *  of `base`. */
  def declarations(base: ElabBase, path: String, files: List[String], decls: List[Item]): ElaboratedDeclarations =
    val core = base.core.fork()
    files.foreach(core.rankFile)
    val reporter = Reporter()
    val env = elab.FileEnv(path, "", base.prelude, base.imports, lintUnused = true, builtinNames = base.builtinNames)
    val e = elab.Elaborator(core, reporter, env, SemanticIndex())
    e.elabDeclarations(decls)
    ElaboratedDeclarations(base, e, e.items.toList, reporter.diagnostics, e.index)

  /** One object item of a program, elaborated against its declarations in a fork of their core. */
  def item(decls: ElaboratedDeclarations, item: Item): ElaboratedItem = observed(decls, item, None)

  /** [[item]], with the reads of the declarations reported to `reads` instead of recorded in the item's
   *  footprint (for the test that the footprint covers every read, [[Unrecorded]]). */
  def observed(decls: ElaboratedDeclarations, item: Item, reads: Option[DeclarationReads]): ElaboratedItem =
    val core = decls.core.fork()
    val reporter = Reporter()
    val e = decls.elaborator.fork(core, reporter, SemanticIndex())
    // the item records its own uses (the declarations' are theirs: an item may be reused with later ones)
    e.state.used = Set.empty
    val footprint = Footprint(DeclarationRanges.of(decls.base.core, decls.core))
    val observer = reads.getOrElse(footprint)
    core.observe(observer)
    e.state.observe(observer)
    try e.elabItemReporting(item)
    finally
      core.observe(null)
      e.state.observe(null)
    val items = e.items.toList
    val parts = e.state.parts.toList
    ElaboratedItem(
      item,
      core,
      items,
      reporter.diagnostics,
      e.index,
      e.state.used.toSet,
      portable(decls.core, core, items, parts),
      parts,
      footprint,
      decls
    )

  /** Whether the items elaborated in `fork` (of `base`) can be moved into another fork of `base`. */
  private def portable(base: Core, fork: Core, items: List[CoreItem], parts: List[elab.ModulePart]): Boolean =
    val levels = base.levels.count
    val partTerms = parts.collect {
      case d: elab.ModulePart.Data => d.data
      case r: elab.ModulePart.Rewrite => r.fn
    }
    fork.moduleInstances.length == base.moduleInstances.length &&
    (base.globals.length until fork.globals.length).forall(id => fork.globals(id).instanceOf.isDefined) &&
    (items.flatMap(CoreItem.terms) ++ partTerms).forall(t =>
      !Tm.exists(t) {
        case Tm.Module(_, _) => true
        case Tm.U1(l) => !l.isConst && l.v >= levels
        case _ => false
      }
    )

  /** A program assembled from its declarations and its object items (in source order): the items are
   *  moved into a fork of the declarations' core (an item that is not portable is elaborated again
   *  there), then the checks across items run. If the items contain a module-wide directive, their rules
   *  and queries are replaced by the expansion of the module (reference: directives): every rule and query then
   *  depends on the expansion, while the items of local directives are kept as elaborated. */
  def assemble(decls: ElaboratedDeclarations, results: List[ElaboratedItem]): (Elaborated, List[Diagnostic], SemanticIndex) =
    val core = decls.core.fork()
    results.map(_.item.span).filter(_.exists).foreach(sp => core.rankFile(sp.source.path))
    val reporter = Reporter()
    val index = SemanticIndex()
    index.include(decls.base.index)
    index.include(decls.index)
    val e = decls.elaborator.fork(core, reporter, index)
    val diagnostics = mutable.ListBuffer.from(decls.base.diagnostics ++ decls.diagnostics)
    val parts = mutable.ListBuffer.empty[elab.ModulePart]
    val elaborated = results.flatMap { r =>
      movable(decls, r, core) match
        case Some(moved) =>
          diagnostics ++= r.diagnostics
          index.include(r.index)
          e.state.used ++= r.used.map(moved.declaration)
          parts ++= r.parts.map(moved.part)
          moved.items(r.items)
        case None =>
          val (beforeItems, beforeParts) = (e.items.length, e.state.parts.length)
          e.elabItemReporting(r.item)
          parts ++= e.state.parts.drop(beforeParts)
          e.items.drop(beforeItems).toList
    }
    val objectItems =
      if !e.rewrites(parts) then elaborated
      else
        elaborated.filter {
          case _: CoreItem.RuleItem | _: CoreItem.QueryItem => false
          case _ => true
        } ++ e.expandModule(parts.toList)
    e.finish()
    diagnostics ++= reporter.diagnostics
    val programItems = decls.items ++ objectItems
    (Elaborated(core, decls.base.items ++ programItems, programItems), diagnostics.toList, index)

  /** How to move a portable item into `to`, a fork of `decls`' core: as it is if it was elaborated
   *  against `decls`, else by the keys of the declarations' globals ([[Rebase]]); `None` if it is not
   *  portable or cannot be moved (it is then elaborated again). The move is done eagerly, so that a meta
   *  or level of the old declarations met in it is found before anything is added to `to`. */
  private def movable(decls: ElaboratedDeclarations, r: ElaboratedItem, to: Core): Option[Moved] =
    if !r.portable then None
    else if r.declarations == null || (r.declarations.nn eq decls) || (r.declarations.nn.core eq decls.core) then
      Some(Moved(decls.core, r.fork, to))
    else
      val old = r.declarations.nn
      val terms = r.items.flatMap(CoreItem.terms) ++ r.parts.flatMap(elab.ModulePart.terms)
      Rebase.declarations(old, decls, r.fork, terms, r.used).flatMap { declaration =>
        val moved = Moved(old.core, r.fork, to, declaration, refuseFrom = (old.base.core.metas.length, old.base.core.levels.count))
        try
          moved.check(r.items, r.parts)
          Some(moved)
        catch case _: Moved.Refused => None
      }

/** Moves the items elaborated in `from` (a fork of `base`) into `to`: if `to` forks `base` too, the
 *  globals and metas of `base` are the same in both; otherwise ([[Rebase]]) `to` forks another
 *  declarations' core over the same libraries, `declaration` maps `base`'s globals into it, and a meta
 *  or universe level of `base` from `refuseFrom` on (one the old declarations created) cannot be moved
 *  ([[Moved.Refused]]). The family instances `from` created are the instances at the same arguments in
 *  `to`, and its metas (the unsolved types of object variables) are created in `to` again. */
private final class Moved(
    base: Core,
    from: Core,
    to: Core,
    val declaration: Int => Int = identity,
    refuseFrom: (Int, Int) = (Int.MaxValue, Int.MaxValue)
):
  private val globals = mutable.HashMap.empty[Int, Int]
  private val metas = mutable.HashMap.empty[Int, Int]

  def items(items: List[CoreItem]): List[CoreItem] = items.map(CoreItem.map(_, term, global))

  def part(p: elab.ModulePart): elab.ModulePart = elab.ModulePart.map(p, term)

  private def term(t: Tm): Tm =
    if refuseFrom._2 != Int.MaxValue && Tm.exists(t) {
        case Tm.U1(l) => !l.isConst && l.v >= refuseFrom._2 && l.v < base.levels.count
        case _ => false
      }
    then throw Moved.Refused()
    Tm.rename(t, global, meta)

  /** Moves everything once (instances and metas are created in `to`); throws [[Moved.Refused]] first if
   *  something cannot be moved. Later calls of [[items]] and [[part]] reuse what was created. */
  def check(items: List[CoreItem], parts: List[elab.ModulePart]): Unit =
    val all = items.flatMap(CoreItem.terms) ++ parts.flatMap(elab.ModulePart.terms)
    all.foreach(t =>
      if Tm.exists(t) {
          case Tm.Meta(m) => m >= refuseFrom._1 && m < base.metas.length
          case _ => false
        }
      then throw Moved.Refused()
    )
    all.foreach(term)

  private def global(id: Int): Int =
    if id < base.globals.length then declaration(id)
    else
      globals.get(id) match
        case Some(g) => g
        case None =>
          val (fam, key) = from.globals(id).instanceOf.get
          val g = to.instanceAt(global(fam), key.map(term))
          globals(id) = g
          g

  private def meta(m: Int): Int =
    if m < base.metas.length then
      if m >= refuseFrom._1 then throw Moved.Refused()
      m
    else
      metas.get(m) match
        case Some(n) => n
        case None =>
          val e = from.metas(m)
          val n = to.newMeta(to.eval(Nil, term(from.quote(0, e.ty))), e.stage, e.span, e.what, e.allowUnsolved)
          metas(m) = n
          e.solution.foreach(v => to.solveMeta(n, to.eval(Nil, term(from.quote(0, v)))))
          n

private object Moved:
  /** An item that refers to a meta or universe level of the declarations it was elaborated against. */
  final class Refused extends Exception(null, null, false, false)
