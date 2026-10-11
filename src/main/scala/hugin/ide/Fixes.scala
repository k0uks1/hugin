package hugin.ide

import hugin.compiler.MetaIndex
import hugin.query.{CompileKey, Database, MetaIde}
import hugin.syntax.{Lexer, Tok}
import hugin.util.{Diagnostic, Reporter, SourceFile, Span}
import hugin.util.diagnostics.Code

/** A text edit: replace the text of `span` by `text`. */
final case class Edit(span: Span, text: String)

/** What a fix is: the fix of a problem, or a rewrite of correct code (interactive development). */
enum FixKind:
  case QuickFix, Rewrite

/** A fix an editor can apply: its title, its edits (possibly in other files than the one it was asked
 *  for), whether an editor may apply it without asking (`preferred`), and the diagnostic it fixes. */
final case class Fix(title: String, kind: FixKind, edits: List[Edit], preferred: Boolean, diagnostic: Option[Diagnostic])

/** Quick fixes and the code actions of interactive development. */
object Fixes:
  /** The fixes for the part `[from, to]` of the file `path` of the program `key`:
   *  - the suggestions of the diagnostics overlapping it ([[hugin.util.diagnostics.Suggestion]]). Only the
   *    first machine-applicable suggestion of a diagnostic is preferred, since editors may apply a
   *    preferred fix without asking; guesses (`MaybeIncorrect`) are only offered. An edit may lie in
   *    another file (a signature); suggestions with edits in the bundled standard library are left out;
   *  - on the meta level, at `from`: add the clauses missing from a function whose coverage error (E0911)
   *    is among those diagnostics, split the pattern variable there, start the clauses of the function
   *    declared there, refine the typed hole there. */
  def at(key: CompileKey, path: String, from: Int, to: Int)(using Database): List[Fix] =
    if Files.isFacts(path) then Nil
    else
      def inFile(span: Span) = span.exists && span.source.path == path
      val here =
        Diagnostics.all(key).filter(d => inFile(d.primarySpan) && d.primarySpan.start <= to && from <= d.primarySpan.end)
      val fixes =
        for
          d <- here
          preferred = d.suggestions.find(_.isMachineApplicable)
          s <- d.suggestions if !s.edits.exists(e => Files.isLibrary(e.span.source.path))
        yield Fix(s.message.capitalize, FixKind.QuickFix, s.edits.map(e => Edit(e.span, e.replacement)), preferred.exists(_ eq s), Some(d))
      fixes ++ meta(key, path, from, here)

  private def meta(key: CompileKey, path: String, from: Int, diagnostics: List[Diagnostic])(using Database): List[Fix] =
    def fix(title: String, kind: FixKind, at: Span, text: String) = Fix(title, kind, List(Edit(at, text)), preferred = false, None)
    val split = MetaIde.splitAt(key, from).flatMap(splitFix)
    val skeleton = MetaIde.skeletonAt(key, from).filter(s => s.decl.source.path == path).map { s =>
      fix(s"Add a clause for `${s.fn}`", FixKind.QuickFix, s.decl.endPoint, "\n" + s.clause)
    }
    val missing =
      for
        d <- diagnostics if d.code == Code.E0911
        m <- MetaIde.missingAt(key, d.primarySpan).toList if m.after.source.path == path
      yield
        val n = m.clauses.length
        val title = if n == 1 then "Add the missing clause" else s"Add the $n missing clauses"
        Fix(title, FixKind.QuickFix, List(Edit(m.after.endPoint, m.clauses.map("\n" + _).mkString)), preferred = true, Some(d))
    val refine = MetaIde.goalAt(key, from).filter(_.span.source.path == path).toList.flatMap { g =>
      g.refinements.map(r => fix(s"Refine the hole with `${r.stripPrefix("(").stripSuffix(")")}`", FixKind.Rewrite, g.span, r))
    }
    missing ++ split.toList ++ skeleton.toList ++ refine

  /** Replaces the clause by one clause per constructor, the variable replaced by the constructor's
   *  pattern where it is bound and where it is used. */
  private def splitFix(s: MetaIndex.Split): Option[Fix] =
    Option.when(s.patterns.nonEmpty && s.clause.exists)(()).map { _ =>
      val text = s.clause.text
      val occurrences = Lexer(SourceFile.virtual("clause", text), Reporter()).tokenize().filter(t => t.kind == Tok.Var && t.text == s.name)
      val indent = " " * (s.clause.start - s.clause.source.lineStart(s.clause.source.lineOf(s.clause.start)))
      val clauses = s.patterns.map { p =>
        occurrences.foldRight(text)((t, acc) => acc.substring(0, t.span.start) + p + acc.substring(t.span.end))
      }
      Fix(s"Split on `${s.name}`", FixKind.Rewrite, List(Edit(s.clause, clauses.mkString("\n" + indent))), preferred = false, None)
    }
