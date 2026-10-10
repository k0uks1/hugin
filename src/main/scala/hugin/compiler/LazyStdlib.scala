package hugin.compiler

import hugin.syntax.{Program, TreeOps}
import hugin.syntax.Trees.{DirArgs, Directive, Ident, Import, Select}
import scala.collection.mutable

/** The lazy re-export of the prelude (reference: modules, "Opening modules"; issue #61): a file that the
 *  prelude opens with a selective `%use "f" (x, …).` is parsed with the prelude (its imports belong to the
 *  import graph, which stays static), but it is elaborated only for a program that may resolve one of the
 *  names it opens. Laziness is allowed only for a file that declares no object constants
 *  ([[StdlibCache.declaresObjects]]): elaborating it creates nothing that the object program contains,
 *  so whether it was elaborated cannot be observed, and the file is elaborated eagerly otherwise.
 *
 *  A program may resolve a name if one of its files (other than the prelude's chain) contains it as a
 *  name, a field or a directive. A name that is similar enough to be suggested for an unknown name
 *  (E0101) counts as well, so that the suggestions do not change. Completion in the language server and
 *  the REPL offers every name in scope, so they elaborate the prelude's chain eagerly. */
object LazyStdlib:
  /** Whether compilations leave out the files they do not use (the differential tests turn it off). */
  @volatile var enabled: Boolean = true

  /** The files of the prelude's chain `std` (in dependency order, the prelude last) that a program whose
   *  other files are `others` (with their paths) elaborates: all of them, except a file that the prelude opens with a
   *  selective `%use` of an import, that no other file imports, that declares no object constants, and
   *  none of whose opened names the program may resolve; the files that only such a file imports are left
   *  out with it (those that the program imports are then its libraries, [[outside]]). */
  def chain(std: List[Parsed], others: List[(String, Program)], builtinNames: Boolean): List[Parsed] =
    std.lastOption match
      case Some(prelude) if enabled && prelude.source.path == SourceLoader.PreludePath =>
        val byPath = std.map(p => p.source.path -> p).toMap
        def importsOf(p: Parsed) = Library.importsOf(p.source.path, p.program).map(_._2)
        val opens = prelude.program.items.collect { case Directive(_, DirArgs.Use(imp: Import, Some(names))) =>
          (ImportPaths.resolve(imp, prelude.source.path), names.map(_.name))
        }
        lazy val written = namesIn(others.map(_._2))
        lazy val importedElsewhere =
          (std.init.flatMap(importsOf) ++ others.flatMap((path, p) => Library.importsOf(path, p).map(_._2))).toSet
        val omitted = opens.collect {
          case (path, names)
              if byPath.contains(path) && importsOf(prelude).count(_ == path) == 1 && !importedElsewhere(path) &&
                !names.exists(mayResolve(written, _)) &&
                !StdlibCache.declaresObjects(std.takeWhile(_.source.path != path), byPath(path), builtinNames) =>
            path
        }.toSet
        if omitted.isEmpty then std
        else
          // the files the prelude still imports, and the files they import
          val kept = mutable.HashSet.empty[String]
          def keep(path: String): Unit =
            if kept.add(path) then byPath.get(path).foreach(importsOf(_).foreach(keep))
          importsOf(prelude).filterNot(omitted).foreach(keep)
          std.filter(p => (p eq prelude) || kept(p.source.path))
      case _ => std

  /** The files of the prelude's chain `std` that [[chain]] left out (`kept` is its result) and that the
   *  program's files `others` import, directly or through each other, in the order of `std`. A file that
   *  only a lazy file imports may be imported by the program as well (`std/list`, which `std/demand`
   *  imports): it is then elaborated as one of the program's libraries, after the prelude, so that the
   *  prelude's chain stays the same for every program that does not use the lazy file. */
  def outside(std: List[Parsed], kept: List[Parsed], others: List[(String, Program)]): List[Parsed] =
    if kept.length == std.length then Nil
    else
      val left = std.filterNot(p => kept.exists(_ eq p)).map(p => p.source.path -> p).toMap
      val needed = mutable.HashSet.empty[String]
      def need(path: String): Unit =
        if left.contains(path) && needed.add(path) then Library.importsOf(path, left(path).program).foreach(i => need(i._2))
      others.foreach((path, p) => Library.importsOf(path, p).foreach(i => need(i._2)))
      std.filter(p => needed(p.source.path))

  /** The program's libraries: the files `rest` after the prelude in the import graph (in dependency
   *  order), with the files `outside` (see [[outside]], with their imports `importsOf`) each placed just
   *  before the first file of `rest` that imports it, or at the end, where the import graph places a file
   *  that only the program imports. So the libraries before it keep their place in the chain. */
  def placed(outside: List[Parsed], rest: List[String], importsOf: String => List[String]): List[String] =
    if outside.isEmpty then rest
    else
      val byPath = outside.map(p => p.source.path -> p).toMap
      val out = mutable.ListBuffer.empty[String]
      val done = mutable.HashSet.empty[String]
      def emit(path: String): Unit =
        if byPath.contains(path) && done.add(path) then
          Library.importsOf(path, byPath(path).program).foreach(i => emit(i._2))
          out += path
      for f <- rest do
        importsOf(f).foreach(emit)
        out += f
      outside.foreach(p => emit(p.source.path))
      out.toList

  /** The names written in `programs`: identifiers, fields and the names of directives. */
  private def namesIn(programs: List[Program]): Set[String] =
    programs.iterator.flatMap(p => TreeOps.nodes(p.items)).collect {
      case Ident(n) => n
      case s: Select => s.name
      case d: Directive => d.kind
    }.toSet

  /** Whether a program that writes `written` may resolve `name`: it writes the name, or a name for which
   *  an unknown name's diagnostic (E0101) might suggest it (the same case of the first letter, and an
   *  edit distance of at most a third of the written name's length, see `Names.similarName`). */
  private def mayResolve(written: Set[String], name: String): Boolean =
    written(name) || {
      val distance = org.apache.commons.text.similarity.LevenshteinDistance.getDefaultInstance
      written.exists { w =>
        val limit = (w.length / 3).max(1)
        w.headOption.map(_.isUpper) == name.headOption.map(_.isUpper) && (w.length - name.length).abs <= limit &&
        distance.apply(w, name).intValue <= limit
      }
    }
