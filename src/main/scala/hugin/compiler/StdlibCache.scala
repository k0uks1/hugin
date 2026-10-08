package hugin.compiler

import hugin.core.{ElabBase, ProgramElab, SourceItems}
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

  /** How many texts are kept. */
  private val capacity = 4

  private val parses = mutable.LinkedHashMap.empty[Key, Parsed]
  private val bases = mutable.LinkedHashMap.empty[(Key, Boolean), (Parsed, ElabBase)]

  /** Whether compilations use the cache (the differential tests turn it off). */
  @volatile var enabled: Boolean = true

  /** Counts elaborations of the prelude by the cache (for tests). */
  @volatile var elaborations: Int = 0

  def isStdlib(path: String): Boolean = path.startsWith(SourceLoader.StdlibPrefix)

  /** The parse of a standard library file with this text: shared, if the cache is enabled. */
  def parsed(path: String, text: String): Parsed =
    if !enabled || !isStdlib(path) then Parsed(SourceFile.virtual(path, text))
    else synchronized(lookup(parses, Key(path, text), Parsed(SourceFile.virtual(path, text))))

  /** The prelude elaborated from `parsed`: shared if `parsed` is the cache's own parse of its text (the
   *  elaborated core refers to the positions of that parse), otherwise elaborated here. */
  def prelude(parsed: Parsed, builtinNames: Boolean): ElabBase =
    def elaborate() =
      elaborations += 1
      ProgramElab.prelude(SourceItems(parsed.source.path, "", parsed.program.items), builtinNames)
    val key = Key(parsed.source.path, parsed.source.content)
    val shared = enabled && synchronized(parses.get(key).exists(_ eq parsed))
    if !shared then elaborate()
    else
      synchronized {
        // a base is used only with the very parse it was elaborated from (the parse may have been
        // dropped and made again since)
        bases.get((key, builtinNames)).filter(_._1 ne parsed).foreach(_ => bases.remove((key, builtinNames)))
        lookup(bases, (key, builtinNames), (parsed, elaborate()))._2
      }

  /** Empties the cache. */
  def clear(): Unit = synchronized {
    parses.clear()
    bases.clear()
  }

  /** The cached value of `key`, computed and stored if missing; the least recently used entry is dropped
   *  when the cache is full. */
  private def lookup[K, V](cache: mutable.LinkedHashMap[K, V], key: K, compute: => V): V =
    val v = cache.remove(key).getOrElse(compute)
    cache(key) = v
    if cache.size > capacity then cache.remove(cache.head._1)
    v
