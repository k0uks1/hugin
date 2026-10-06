package hugin.query

import hugin.compiler.{DiagnosticPart, Reported}
import hugin.syntax.Trees.{Decl, Def}
import hugin.util.*

/** The diagnostics of one file of a compilation, in the order the compiler reports them. */
final case class FileDiagnostics(path: String, diagnostics: List[Diagnostic])

/** The diagnostics of a compilation by file (step 10 of `docs/INCREMENTALITY.md`): the program's files and
 *  each library it includes, in the order of their paths, each with its diagnostics in the order of the
 *  compiler's output; concatenated, they are the compilation's output ([[Compiled.diagnostics]]).
 *
 *  The diagnostics of the elaboration are read from the accumulators of the queries that computed them,
 *  not from the compilation: a library's naming and elaboration ([[LibraryDiagnostics]], pushed by
 *  [[NameLibrary]] and [[ElabLibrary]], once per library and shared by every program importing it) and
 *  the program's naming, signatures and items ([[ProgramDiagnostics]], pushed by [[ScopeOf]],
 *  [[Signatures]] and every [[ElabItem]]). The compilation contributes only what its own phases reported
 *  (parse and import errors, the object-level phases) and the order in which it reported the parts
 *  ([[hugin.compiler.Context.reported]]), which the output is assembled in, with the compiler's
 *  deduplication, placement in the current text and ordering. */
object FileDiagnostics:
  /** The diagnostics of the compilation `key` by file. */
  def of(key: CompileKey)(using db: Database): List[FileDiagnostics] =
    val compiled = db(Compile, key)
    val ctx = compiled.context
    val reporter = Reporter()
    for entry <- ctx.reported do
      entry match
        case Reported.Own(d) => reporter.report(ctx.placed(d))
        case Reported.Part(part) => ofPart(part).foreach(d => reporter.report(ctx.placed(d)))
    // the output is sorted by path first, so the diagnostics of a file are consecutive
    val sorted = reporter.sorted
    val paths = sorted.map(_.primarySpan.source.path).distinct
    val byPath = sorted.groupBy(_.primarySpan.source.path)
    paths.map(p => FileDiagnostics(p, byPath(p)))

  /** The diagnostics of the compilation `key` in the file `path` (none if it has none). */
  def in(key: CompileKey, path: String)(using db: Database): List[Diagnostic] =
    of(key).find(_.path == path).fold(Nil)(_.diagnostics)

  /** The diagnostics of a part of the elaboration, from the accumulators of the queries computing it, in
   *  the order the compiler reports them. */
  def ofPart(part: DiagnosticPart)(using db: Database): Vector[Diagnostic] = part match
    case DiagnosticPart.LibraryNames(key) => db.pushed(LibraryDiagnostics, NameLibrary, key)
    case DiagnosticPart.LibraryElab(key) => db.pushed(LibraryDiagnostics, ElabLibrary, key)
    case DiagnosticPart.ProgramNames(root, prelude) => db.pushed(ProgramDiagnostics, ScopeOf, ProgramKey(root, prelude))
    case DiagnosticPart.ProgramElab(root, prelude) =>
      val program = ProgramKey(root, prelude)
      // as `ElabFile` assembles them: the signatures', then each other item's, in item order
      val items = db(ProgramItemsOf, program).items.collect {
        case (k, item) if !item.isInstanceOf[Decl] && !item.isInstanceOf[Def] => k
      }
      db.pushed(ProgramDiagnostics, Signatures, program) ++
        items.flatMap(k => db.pushed(ProgramDiagnostics, ElabItem, ItemQueryKey(program, k)))
