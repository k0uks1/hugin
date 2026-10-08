package hugin.cli

import hugin.compiler.Display
import hugin.query.*
import hugin.util.Diagnostic
import hugin.util.diagnostics.Fixes

/** `hugin fix FILE`: applies the machine-applicable suggestions of the diagnostics shown (with the lint
 *  levels of `display`) to the file and recompiles, until no suggestion is left or [[MaxRounds]] rounds
 *  have run, as `cargo fix` does. */
object Fix:
  /** Rounds of fixing; each round applies every suggestion that does not touch another. */
  val MaxRounds = 10

  /** The fixed text, the number of suggestions applied, and the diagnostics of the fixed text (before the
   *  lint levels apply). */
  final case class Outcome(text: String, applied: Int, diagnostics: List[Diagnostic])

  /** Fixes the text of `key.path` in `db` (which holds the original text), updating it in `db`. */
  def run(key: CompileKey, display: Display)(using db: Database): Outcome =
    def go(text: String, applied: Int, round: Int): Outcome =
      val diags = db(Compile, key).diagnostics
      val fixes = if round == MaxRounds then Nil else Fixes.applicable(display.shown(diags), key.path)
      if fixes.isEmpty then Outcome(text, applied, diags)
      else
        val fixed = Fixes.apply(text, fixes.flatMap(_.edits))
        db.set(SourceText, key.path, fixed)
        go(fixed, applied + fixes.length, round + 1)
    go(db.get(SourceText, key.path), 0, 0)
