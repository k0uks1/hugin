package hugin.util.diagnostics

import hugin.util.Span

/** How safely a tool may apply a suggestion (rustc's `Applicability`). There is deliberately no
 *  "unspecified": every suggestion states it, so that [[MachineApplicable]] can be trusted. */
enum Applicability:
  /** Preserves the meaning or is certainly what was intended: editors mark it preferred, and a `fix`
   *  command may apply it without asking. */
  case MachineApplicable

  /** A plausible guess (a spelling correction): offered, never applied automatically. */
  case MaybeIncorrect

  /** Contains `_` holes or `...` that the user must fill in. */
  case HasPlaceholders

/** Replace the text of `span` by `replacement`; an empty span inserts. */
final case class Edit(span: Span, replacement: String)

/** A fix of a diagnostic: `message` names the edit as a command (``replace `X` with `_` ``). The edits may
 *  lie in other files than the diagnostic (a signature a requirement is missing from). */
final case class Suggestion(message: String, edits: List[Edit], applicability: Applicability):
  def isMachineApplicable: Boolean = applicability == Applicability.MachineApplicable

  /** Whether every edit has source text to edit (generated code has none). */
  def isApplicable: Boolean = edits.nonEmpty && edits.forall(_.span.exists)

  def mapSpans(f: Span => Span): Suggestion = copy(edits = edits.map(e => e.copy(span = f(e.span))))

object Suggestion:
  /** A suggestion of a single edit. */
  def replace(span: Span, replacement: String, message: Msg, applicability: Applicability): Suggestion =
    Suggestion(message.plain, List(Edit(span, replacement)), applicability)
