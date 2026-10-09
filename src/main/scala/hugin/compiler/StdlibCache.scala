package hugin.compiler

import hugin.core.{CoreItem, ElabBase, GlobalKind, ProgramElab, SourceItems, Val}
import hugin.syntax.Trees.{Clause, Decl, Def, DirArgs, Directive, Import}
import hugin.util.SourceFile
import scala.collection.mutable

/** The bundled standard library (the prelude), parsed and elaborated once per process (issue #60): every
 *  compilation in a JVM (each `hugin` command, every query database of a test suite, the REPL and the
 *  language server) shares one parse and one elaborated core of each text of a standard library file,
 *  instead of elaborating the prelude again for each.
 *
 *  Sound because both results are pure functions of their inputs, all of which are part of the key: the
 *  file's path and its whole text (compared in full on a hit), and for the elaboration the
 *  `builtinNames` flag; the compiler's code is that of the running JVM. Nothing that uses the shared
 *  results changes them: a parse is immutable (a library file is parsed as a whole, it is never split
 *  into slices whose placement changes), and an elaborated base is only ever *forked* by later parts
 *  (`ProgramElab`; the query database already shares a base between programs in the same way). The
 *  differential tests (`StdlibCacheSuite`) compile the golden programs with and without the cache and
 *  check that the shared base is unchanged afterwards.
 *
 *  The cache keeps the last few texts (an editor may change the prelude), so it stays small. */
object StdlibCache:
  private final case class Key(path: String, text: String)

  /** How many texts are kept: of each file of the standard library, and some edited versions. */
  private val capacity = 64

  private val parses = mutable.LinkedHashMap.empty[Key, Parsed]
  private val bases = mutable.LinkedHashMap.empty[(List[Key], Boolean), (List[Parsed], ElabBase)]
  private val objects = mutable.LinkedHashMap.empty[(List[Key], Boolean), (List[Parsed], Boolean)]

  /** Whether compilations use the cache (the differential tests turn it off). */
  @volatile var enabled: Boolean = true

  /** Counts elaborations of the prelude by the cache (for tests). */
  @volatile var elaborations: Int = 0

  def isStdlib(path: String): Boolean = path.startsWith(SourceLoader.StdlibPrefix)

  /** The parse of a standard library file with this text: shared, if the cache is enabled. */
  def parsed(path: String, text: String): Parsed =
    if !enabled || !isStdlib(path) then Parsed(SourceFile.virtual(path, text))
    else synchronized(lookup(parses, Key(path, text), Parsed(SourceFile.virtual(path, text))))

  /** The prelude elaborated from `chain`: the files it imports in dependency order, then the prelude
   *  itself (reference: prelude). Shared if every parse is the cache's own parse of its text (the
   *  elaborated core refers to the positions of those parses), otherwise elaborated here. The files
   *  before the prelude are shared one by one, each with the files before it: chains that leave out a
   *  file the prelude re-exports lazily ([[LazyStdlib]]) share the files before it. */
  def prelude(chain: List[Parsed], builtinNames: Boolean): ElabBase =
    memo(chain, builtinNames) {
      elaborations += 1
      ProgramElab.preludeOn(libraries(chain.init, builtinNames), items(chain.last))
    }

  /** The files `files` of the standard library (in dependency order, without the prelude) elaborated one
   *  after the other, each file once per process and chain before it. */
  def libraries(files: List[Parsed], builtinNames: Boolean): ElabBase =
    if files.isEmpty then ProgramElab.empty(builtinNames)
    else memo(files, builtinNames)(ProgramElab.library(libraries(files.init, builtinNames), items(files.last)))

  /** Whether the file `file` of the standard library, after the files `before`, declares or may declare
   *  object constants: a lazy re-export ([[LazyStdlib]]) is allowed only if it does not. Decided from its
   *  declarations, elaborated without the clauses of its functions (cheap, [[ProgramElab.signatures]]): a
   *  file declares none if its items are declarations, definitions, clauses, and `%use` of imported
   *  files, `%infix` and `%export`; its declarations are not object constants or shared data, those with
   *  a definition are not modules (a functor's application creates the module's relations), and the
   *  declarations elaborate without errors (which are then reported). */
  def declaresObjects(before: List[Parsed], file: Parsed, builtinNames: Boolean): Boolean =
    val chain = before :+ file
    def compute: Boolean =
      val plain = file.program.items.forall {
        case d: Decl => d.sup.isEmpty
        case _: Clause | _: Def => true
        case Directive(_, DirArgs.Use(_: Import, _) | _: DirArgs.Infix | _: DirArgs.Export) => true
        case _ => false
      }
      !plain || {
        val defined = file.program.items.collect {
          case d: Decl if d.defn.isDefined => d.name.name
          case d: Def => d.name.name
        }.toSet
        val base = libraries(before, builtinNames)
        val after = ProgramElab.signatures(base, items(file))
        val core = after.core
        after.diagnostics.length > base.diagnostics.length ||
        after.items.drop(base.items.length).exists(!_.isInstanceOf[CoreItem.GlobalItem]) ||
        (base.core.globals.length until core.globals.length).exists { id =>
          val g = core.globals(id)
          g.kind match
            case GlobalKind.Object(_) | GlobalKind.Family(_, _) => true
            case _ => defined(g.name) && core.force(g.ty).isInstanceOf[Val.RecTy]
        }
      }
    val keys = chain.map(key)
    if !enabled || !synchronized(own(chain, keys)) then compute
    else synchronized(lookup(objects, (keys, builtinNames), (chain, compute))._2)

  private def items(p: Parsed) = SourceItems(p.source.path, "", p.program.items)

  private def key(p: Parsed) = Key(p.source.path, p.source.content)

  /** Whether every parse of `chain` is the cache's own parse of its text. */
  private def own(chain: List[Parsed], keys: List[Key]): Boolean = chain.zip(keys).forall((p, k) => parses.get(k).exists(_ eq p))

  /** The base elaborated from `chain` by `compute`: shared if the cache is enabled and every parse is
   *  its own, since the elaborated core refers to the positions of those parses. */
  private def memo(chain: List[Parsed], builtinNames: Boolean)(compute: => ElabBase): ElabBase =
    val keys = chain.map(key)
    if !enabled || !synchronized(own(chain, keys)) then compute
    else
      synchronized {
        // a base is used only with the very parses it was elaborated from (a parse may have been dropped
        // and made again since)
        bases.get((keys, builtinNames)).filter(b => b._1.zip(chain).exists(_ ne _)).foreach(_ => bases.remove((keys, builtinNames)))
        lookup(bases, (keys, builtinNames), (chain, compute))._2
      }

  /** The bundled prelude with the text `text` (by default its own) and the bundled files it imports, in
   *  dependency order, parsed through the cache: what [[prelude]] elaborates (for tests and benchmarks;
   *  compilations take the chain from their import graph). */
  def bundledChain(text: String = SourceLoader.stdlib(SourceLoader.PreludePath).get): List[Parsed] =
    val prelude = parsed(SourceLoader.PreludePath, text)
    val out = mutable.ListBuffer.empty[Parsed]
    val seen = mutable.HashSet(SourceLoader.PreludePath)
    def visit(path: String, p: Parsed): Unit =
      for (_, dep) <- Library.importsOf(path, p.program) if seen.add(dep) do
        SourceLoader.stdlib(dep).foreach { t =>
          val q = parsed(dep, t)
          visit(dep, q)
          out += q
        }
    visit(SourceLoader.PreludePath, prelude)
    out.toList :+ prelude

  /** Empties the cache. */
  def clear(): Unit = synchronized {
    parses.clear()
    bases.clear()
    objects.clear()
  }

  /** The cached value of `key`, computed and stored if missing; the least recently used entry is dropped
   *  when the cache is full. */
  private def lookup[K, V](cache: mutable.LinkedHashMap[K, V], key: K, compute: => V): V =
    val v = cache.remove(key).getOrElse(compute)
    cache(key) = v
    if cache.size > capacity then cache.remove(cache.head._1)
    v
