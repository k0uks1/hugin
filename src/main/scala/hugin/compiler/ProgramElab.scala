package hugin.compiler

import hugin.meta.*
import hugin.syntax.{Program, Tree}
import hugin.syntax.Trees.*
import hugin.util.*
import scala.collection.mutable

/** The text and position of an item, for comparing items with their positions: the tree (whose equality
 *  ignores spans), the file, the item's offsets, its first line and the text of all lines it touches. Two
 *  items with equal fingerprints have the same spans, and every position inside them has the same line,
 *  column and line text, so results computed from one are valid for the other, also where they keep spans
 *  into the source file the first one was parsed from. Until items are parsed from their own slices (step
 *  9 of `docs/INCREMENTALITY.md`), an edit before an item changes its fingerprint. */
final case class ItemFingerprint(tree: Item, path: String, start: Int, end: Int, line: Int, text: String)

object ItemFingerprint:
  def of(item: Item): ItemFingerprint =
    val sp = item.span
    if !sp.exists then ItemFingerprint(item, "", 0, 0, 0, "")
    else
      val src = sp.source
      val first = src.lineOf(sp.start)
      val last = src.lineOf(sp.end)
      val to = if last + 1 < src.lineCount then src.lineStart(last + 1) else src.content.length
      ItemFingerprint(item, src.path, sp.start, sp.end, first, src.content.substring(src.lineStart(first), to))

/** Equality of typing results that also compares positions: spans by file and offsets (not by the
 *  identity of their source file, which is new after every parse), symbols by key, kind and position,
 *  scopes by key, and the spans that object trees keep apart from their fields. Anything else (such as
 *  type parameters, which have an identity) compares with `==`. */
object Positional:
  def same(a: Any, b: Any): Boolean = (a, b) match
    case (x: Span, y: Span) => x.start == y.start && x.end == y.end && x.source.path == y.source.path
    case (x: Sym, y: Sym) => x.key == y.key && x.kind == y.kind && same(x.span, y.span)
    case (x: Scope, y: Scope) => x.key == y.key
    case (x: hugin.obj.Term, y: hugin.obj.Term) => same(x.span, y.span) && fields(x.asInstanceOf[Product], y.asInstanceOf[Product])
    case (x: hugin.obj.Formula, y: hugin.obj.Formula) => same(x.span, y.span) && fields(x.asInstanceOf[Product], y.asInstanceOf[Product])
    case (x: hugin.obj.Rule, y: hugin.obj.Rule) =>
      same(x.span, y.span) && same(x.origin, y.origin) && same(x.expansions, y.expansions) && fields(x, y)
    case (x: hugin.obj.Query, y: hugin.obj.Query) =>
      same(x.span, y.span) && same(x.origin, y.origin) && same(x.expansions, y.expansions) && fields(x, y)
    case (x: hugin.obj.Directive, y: hugin.obj.Directive) => same(x.span, y.span) && same(x.origin, y.origin) && fields(x, y)
    case (x: Tree, y: Tree) => x == y && same(x.span, y.span)
    case (x: collection.Map[?, ?], y: collection.Map[?, ?]) =>
      val ym = y.asInstanceOf[collection.Map[Any, Any]]
      x.size == y.size && x.forall((k, v) => ym.get(k).exists(same(v, _)))
    case (x: collection.Set[?], y: collection.Set[?]) => x == y
    case (x: Iterable[?], y: Iterable[?]) =>
      val (i, j) = (x.iterator, y.iterator)
      var ok = true
      while ok && i.hasNext && j.hasNext do ok = same(i.next(), j.next())
      ok && !i.hasNext && !j.hasNext
    case (x: Product, y: Product) => fields(x, y)
    case _ => a == b

  private def fields(x: Product, y: Product): Boolean =
    x.getClass == y.getClass && x.productArity == y.productArity &&
      (0 until x.productArity).forall(i => same(x.productElement(i), y.productElement(i)))

/** The declarations an item of a program can depend on: a top-level declaration or definition of the
 *  program (with everything elaborated inside it), or a symbol of a library whose results the program
 *  changed (a `%mode` of a prelude formula function). */
enum SigOwner:
  case Item(key: ItemKey)
  case Library(sym: SymKey)

/** What an item sees of one declaration ([[SigOwner]]): the fingerprints of the declaring item and of the
 *  clauses of a formula function, and the typing results of its symbols (compared with positions). */
final class DeclSigValue(
    val fingerprints: List[ItemFingerprint],
    val results: Map[SymKey, (Sym, SymSnapshot)],
    val paramTypes: Map[SymKey, Tree]
):
  override def equals(that: Any): Boolean = that match
    case d: DeclSigValue =>
      fingerprints == d.fingerprints && paramTypes == d.paramTypes && Positional.same(results, d.results)
    case _ => false
  override def hashCode: Int = fingerprints.hashCode

object DeclSigValue:
  val empty: DeclSigValue = DeclSigValue(Nil, Map.empty, Map.empty)

/** A program's top level after naming: its scope (frozen) with the symbols of its declarations, their keys
 *  and the namer's diagnostics. `declarations` are the `Decl` and `Def` items with their keys, `fnModes`
 *  the `%mode` directives that name a formula function (their modes are typing results of the function).
 *
 *  Equal when the items the namer and the elaboration of declarations read are equal with their positions
 *  (`fingerprint`: declarations, clauses of formula functions, `%mode`s of formula functions) and the
 *  enclosing prelude scope is the same: a memoised naming then stays valid, also its symbols' spans. */
final class NamedProgram(
    val source: SourceFile,
    val scope: Scope,
    val keys: SymKeys,
    val diagnostics: List[Diagnostic],
    val declarations: List[(ItemKey, Item)],
    val fnModes: List[Item],
    val fingerprint: List[ItemFingerprint]
):
  override def equals(that: Any): Boolean = that match
    case n: NamedProgram =>
      scope.key == n.scope.key && fingerprint == n.fingerprint && scope.parent.zip(n.scope.parent).forall(_ eq _)
    case _ => false
  override def hashCode: Int = fingerprint.hashCode

/** The libraries of a program (the prelude and its imported files, in dependency order), elaborated. */
final class ProgramLibraries(val elaborated: List[ElaboratedLibrary]):
  override def equals(that: Any): Boolean = that match
    case p: ProgramLibraries => p.elaborated.length == elaborated.length && p.elaborated.zip(elaborated).forall(_ eq _)
    case _ => false
  override def hashCode: Int = elaborated.length

/** The declarations and definitions of a program, elaborated together in item order (the "signatures"
 *  the other items are elaborated against): their elaborated items, typing results (frozen), symbol keys,
 *  part of the semantic index, scopes of module bodies and diagnostics, and the results split by
 *  declaration (`parts`), which is what an item depends on. */
final class ProgramSignatures(
    val items: Map[ItemKey, List[EItem]],
    val table: SymTable,
    val keys: SymKeys,
    val index: SemanticIndex,
    val scopes: List[(ScopeKey, Scope)],
    val diagnostics: List[Diagnostic],
    val parts: Map[SigOwner, DeclSigValue]
)

/** One top-level item (a rule, query, directive or subtyping edge) of a program, elaborated: its
 *  elaborated items, typing results of the symbols it created, their keys, its part of the semantic
 *  index, scopes of module bodies and diagnostics. */
final class ElaboratedItem(
    val key: ItemKey,
    val items: List[EItem],
    val table: SymTable,
    val keys: SymKeys,
    val index: SemanticIndex,
    val scopes: List[(ScopeKey, Scope)],
    val diagnostics: List[Diagnostic]
)

/** A program's top level, elaborated: what the typer phase used to compute in one traversal. */
final class ElaboratedProgram(
    val body: MExpr,
    val table: SymTable,
    val keys: SymKeys,
    val index: SemanticIndex,
    val scopes: List[(ScopeKey, Scope)],
    val diagnostics: List[Diagnostic]
)

/** Per-item elaboration of a program (step 8 of `docs/INCREMENTALITY.md`). The program's top level is
 *  named once ([[name]]); its declarations and definitions are elaborated together, in item order
 *  ([[signatures]]); every other item (rules, queries, directives, subtyping edges) is elaborated on its
 *  own against them ([[item]]), and the results are assembled in item order ([[assemble]]). The query
 *  database memoises each part (`hugin.query`); [[direct]] computes them in sequence.
 *
 *  An item sees exactly what it would see if the whole body were elaborated in item order: object
 *  declarations and type definitions are elaborated on demand anyway, and the meta definitions and
 *  formula functions of later items are hidden from it (they read as not elaborated yet), which gives the
 *  forward-reference error E0105 that the elaboration in item order gave. */
object ProgramElab:
  private def context(source: SourceFile, prelude: Boolean, libs: Libraries, plibs: ProgramLibraries): Context =
    val ctx = Context(CompilationUnit(source), Settings(prelude = prelude), Reporter(), libs)
    for e <- plibs.elaborated do
      val lib = Library(e.key, e.named.parsed)
      lib.named = e.named
      lib.elaborated = e
      ctx.unit.libraries(e.key.path) = lib
    ctx

  /** Whether a rule is (or is meant as) a clause of a formula function of `scope`: one of its heads applies
   *  a formula function declared there (the namer collects these, see [[Namer.enter]]). */
  private def namesFormulaFn(r: Rule, scope: Scope): Boolean =
    def headName(t: Tree): Option[String] = t match
      case Ident(n) => Some(n)
      case Apply(f, _) => headName(f)
      case _ => None
    r.heads.exists(h => headName(h).flatMap(scope.lookupLocal).exists(_.kind == SymKind.FormulaFn))

  /** Names the top level of the program `program` (the file `root`). */
  def name(root: String, source: SourceFile, program: Program, prelude: Boolean, libs: Libraries): NamedProgram =
    val ctx = Context(CompilationUnit(source), Settings(prelude = prelude), Reporter(), libs)
    val scope = Scope(Some(Library.preludeScope(prelude, libs)), "program", ScopeKey.File(root))
    Namer.enter(program.items, scope)(using ctx)
    scope.freeze()
    val keyed = program.items.zip(ItemKey.assign(scope.key, program.items))
    val declarations = keyed.filter((item, _) => item.isInstanceOf[Decl] || item.isInstanceOf[Def]).map(_.swap)
    def isFnMode(item: Item) = item match
      case Directive(_, DirArgs.Mode(Ident(n), _)) => scope.lookup(n).exists(_.kind == SymKind.FormulaFn)
      case _ => false
    val fnModes = program.items.filter(isFnMode)
    val read = program.items.filter {
      case _: Decl | _: Def => true
      case r: Rule => namesFormulaFn(r, scope)
      case d => isFnMode(d)
    }
    NamedProgram(source, scope, ctx.unit.symKeys, ctx.reporter.diagnostics, declarations, fnModes, read.map(ItemFingerprint.of))

  /** The libraries of a program, elaborated, as the imports phase and the typer phase include them. */
  def libraries(root: String, program: Program, prelude: Boolean, libs: Libraries): ProgramLibraries =
    val graph = libs.graph(root, program, prelude)
    val cut = graph.cut.filter((f, _) => graph.files.contains(f))
    ProgramLibraries(graph.files.map(p => libs.elaborated(LibraryKey(p, prelude, cut).at(p))))

  /** The top-level item declaring the symbol with key `key` of the program whose scope is `root`, if the
   *  symbol belongs to one: a top-level declaration or a symbol bound inside one. */
  private def ownerOf(root: Scope, key: SymKey): Option[ItemKey] =
    if key.scope == root.key then root.decls.get(key.name).flatMap(_.item) else scopeOwner(root, key.scope)

  private def scopeOwner(root: Scope, scope: ScopeKey): Option[ItemKey] = scope match
    case ScopeKey.File(_) => None
    case ScopeKey.Module(o, _) => if o.scope == root.key then Some(o) else scopeOwner(root, o.scope)
    case ScopeKey.Local(o, _) => if o.scope == root.key then Some(o) else scopeOwner(root, o.scope)
    case ScopeKey.Params(s) => ownerOf(root, s)

  /** Elaborates the declarations and definitions of a named program. */
  def signatures(named: NamedProgram, plibs: ProgramLibraries, prelude: Boolean, libs: Libraries): ProgramSignatures =
    val ctx = context(named.source, prelude, libs, plibs)
    val u = ctx.unit
    u.symKeys.inherit(named.keys)
    plibs.elaborated.foreach(e => u.symKeys.inherit(e.keys))
    val typer = hugin.meta.typer.Typer(ctx, plibs.elaborated.map(_.symbols))
    val items = typer.elabDeclarations(named.declarations, named.scope, named.fnModes)
    typer.syms.freeze()
    u.scopes.values.foreach(_.freeze())
    // the results by declaration
    val results = mutable.HashMap.empty[SigOwner, mutable.HashMap[SymKey, (Sym, SymSnapshot)]]
    val params = mutable.HashMap.empty[SigOwner, mutable.HashMap[SymKey, Tree]]
    def owner(s: Sym): SigOwner = ownerOf(named.scope, s.key).fold(SigOwner.Library(s.key))(SigOwner.Item(_))
    for (s, r) <- typer.syms.localResults do results.getOrElseUpdate(owner(s), mutable.HashMap.empty)(s.key) = (s, r)
    for (p, t) <- typer.syms.localParamTypes do params.getOrElseUpdate(owner(p), mutable.HashMap.empty)(p.key) = t
    val declaring = named.scope.decls.values.toList.flatMap(s => s.item.map(_ -> s)).groupMap(_._1)(_._2)
    val fingerprints: Map[SigOwner, List[ItemFingerprint]] = named.declarations.map { (k, item) =>
      val clauses = declaring.getOrElse(k, Nil).flatMap(_.clauses)
      (SigOwner.Item(k): SigOwner) -> (item :: clauses).map(ItemFingerprint.of)
    }.toMap
    val parts = (fingerprints.keySet ++ results.keySet ++ params.keySet).iterator.map { o =>
      o -> DeclSigValue(
        fingerprints.getOrElse(o, Nil),
        results.get(o).fold(Map.empty)(_.toMap),
        params.get(o).fold(Map.empty)(_.toMap)
      )
    }.toMap
    ProgramSignatures(items.toMap, typer.syms, u.symKeys, u.index, u.scopes.toList, ctx.reporter.diagnostics, parts)

  /** What an item reads of the declarations it is elaborated against: the meta definitions and formula
   *  functions of later items are hidden, and every declaration whose results are read is recorded. */
  private final class ItemView(root: Scope, sigs: SymTable, later: Set[ItemKey]) extends SymTable.View:
    val observed: mutable.LinkedHashSet[SigOwner] = mutable.LinkedHashSet.empty
    def hidden(s: Sym): Boolean = (s.kind == SymKind.MetaDef || s.kind == SymKind.FormulaFn) && s.item.exists(later)
    def observe(s: Sym): Unit =
      ownerOf(root, s.key) match
        case Some(k) => observed += SigOwner.Item(k)
        case None => if sigs.hasLocal(s) then observed += SigOwner.Library(s.key)

  /** Elaborates one top-level item (not a declaration or definition) of a named program against its
   *  signatures; `later` are the keys of the declarations and definitions after it. Returns the item and
   *  the declarations it read. */
  def item(
      named: NamedProgram,
      sigs: ProgramSignatures,
      plibs: ProgramLibraries,
      key: ItemKey,
      item: Item,
      later: Set[ItemKey],
      prelude: Boolean,
      libs: Libraries
  ): (ElaboratedItem, Set[SigOwner]) =
    val ctx = context(named.source, prelude, libs, plibs)
    val u = ctx.unit
    u.symKeys.inherit(sigs.keys)
    val view = ItemView(named.scope, sigs.table, later)
    val typer = hugin.meta.typer.Typer(ctx, List(sigs.table), view)
    val out = named.scope.observing(view.observe)(typer.elabTopItem(item, key, named.scope))
    typer.syms.freeze()
    u.scopes.values.foreach(_.freeze())
    (ElaboratedItem(key, out, typer.syms, u.symKeys, u.index, u.scopes.toList, ctx.reporter.diagnostics), view.observed.toSet)

  /** The keys of the declarations and definitions after each item, by item. */
  def laterDeclarations(items: List[(ItemKey, Item)]): Map[ItemKey, List[ItemKey]] =
    var after = List.empty[ItemKey]
    val out = mutable.HashMap.empty[ItemKey, List[ItemKey]]
    for (k, item) <- items.reverse do
      out(k) = after
      item match
        case _: Decl | _: Def => after = k :: after
        case _ =>
    out.toMap

  /** Assembles the program from its parts, in item order. */
  def assemble(
      named: NamedProgram,
      sigs: ProgramSignatures,
      items: List[(ItemKey, Item)],
      elaborated: ItemKey => ElaboratedItem,
      span: Span
  ): ElaboratedProgram =
    val index = SemanticIndex()
    index.scope(span, named.scope)
    index.include(sigs.index)
    val table = SymTable(List(sigs.table))
    val keys = SymKeys()
    keys.inherit(sigs.keys)
    val scopes = mutable.ListBuffer.from(sigs.scopes)
    val diagnostics = mutable.ListBuffer.from(sigs.diagnostics)
    val body = items.flatMap { (k, item) =>
      item match
        case _: Decl | _: Def => sigs.items.getOrElse(k, Nil)
        case _ =>
          val e = elaborated(k)
          table.absorb(e.table)
          keys.absorb(e.keys)
          index.include(e.index)
          scopes ++= e.scopes
          diagnostics ++= e.diagnostics
          e.items
    }
    table.freeze()
    ElaboratedProgram(MExpr.Body(body, named.scope, span), table, keys, index, scopes.toList, diagnostics.toList)

  /** Elaborates the top level of a named program, every part in sequence (no memoisation). */
  def direct(root: String, program: Program, prelude: Boolean, named: NamedProgram, libs: Libraries): ElaboratedProgram =
    val plibs = libraries(root, program, prelude, libs)
    val sigs = signatures(named, plibs, prelude, libs)
    val items = program.items.zip(ItemKey.assign(named.scope.key, program.items)).map(_.swap)
    val later = laterDeclarations(items).view.mapValues(_.toSet).toMap
    val elaborated = items.collect {
      case (k, i) if !i.isInstanceOf[Decl] && !i.isInstanceOf[Def] =>
        k -> item(named, sigs, plibs, k, i, later(k), prelude, libs)._1
    }.toMap
    assemble(named, sigs, items, elaborated, program.span)
