package hugin.util.diagnostics

import hugin.util.Diagnostic

/** Applying suggestions to source text, as `hugin fix` does (rustfix). Only [[Applicability.MachineApplicable]]
 *  suggestions are applied, and only those whose edits all lie in the file being fixed: a suggestion that
 *  also edits another file (a library's signature) is left for the user. */
object Fixes:
  /** The machine-applicable suggestions of `ds` that can be applied to the file `path` together, in order:
   *  a suggestion is taken if none of its edits touches an edit taken before (the first one wins; the
   *  others are reconsidered after recompiling). */
  def applicable(ds: List[Diagnostic], path: String): List[Suggestion] =
    val candidates = ds.flatMap(_.suggestions).filter(s => s.isMachineApplicable && s.edits.forall(_.span.source.path == path))
    candidates.foldLeft(Vector.empty[Suggestion]) { (taken, s) =>
      if s.edits.exists(e => taken.exists(_.edits.exists(touches(_, e)))) then taken else taken :+ s
    }.toList

  /** Whether two edits overlap or are adjacent (then their order would matter). */
  def touches(a: Edit, b: Edit): Boolean = a.span.start <= b.span.end && b.span.start <= a.span.end

  /** `text` with the edits applied. The edits must not touch each other; they are applied from the last
   *  to the first, so that every offset refers to the original text. */
  def apply(text: String, edits: List[Edit]): String =
    edits.sortBy(-_.span.start).foldLeft(text)((t, e) => t.substring(0, e.span.start) + e.replacement + t.substring(e.span.end))
