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
   *  out with it. */
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
      written.exists { w =>
        val limit = (w.length / 3).max(1)
        w.headOption.map(_.isUpper) == name.headOption.map(_.isUpper) && (w.length - name.length).abs <= limit &&
        hugin.util.Levenshtein.distance(w, name) <= limit
      }
    }
