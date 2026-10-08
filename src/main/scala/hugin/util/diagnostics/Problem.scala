package hugin.util.diagnostics

import hugin.util.{Diagnostic, Label, Origin, Severity, Span}

/** Something a phase reports. Each phase declares its problems as one enum extending `Problem` (in a
 *  `*Problems.scala` file): that enum is the phase's inventory, and each case holds the data the
 *  diagnostic needs and defines its wording once.
 *
 *  A call site reports a value: `ctx.report(NameError.Duplicate(name, first))`. Conversion to the plain
 *  [[Diagnostic]] is eager (see [[toDiagnostic]]), so the query database never stores compiler symbols in
 *  diagnostics. */
trait Problem:
  def code: Code

  /** The smallest span that shows the problem. */
  def primary: Span

  /** The headline: what is wrong, lowercase, without a final period. */
  def message: Msg

  /** What is wrong at [[primary]]. */
  def primaryLabel: Msg = Msg.empty

  /** Related places, each with why it matters ("first declared here"). */
  def labels: List[(Span, Msg)] = Nil

  /** Facts explaining why it is an error. */
  def notes: List[Msg] = Nil

  /** What to do. */
  def helps: List[Msg] = Nil

  /** Edits fixing the problem, each with its applicability. */
  def suggestions: List[Suggestion] = Nil

  /** The meta-level expansion chain of generated code the problem lies in. */
  def origin: Origin = Origin.Source

  def severity: Severity = code.level.severity

  /** The diagnostic: the primary label first, then the secondary labels in order. Suggestions without
   *  source text to edit are dropped. */
  final def toDiagnostic: Diagnostic =
    Diagnostic(
      severity,
      code,
      message.plain,
      Label(primary, primaryLabel.plain, primary = true) :: labels.map((s, m) => Label(s, m.plain, primary = false)),
      notes.map(_.plain),
      helps.map(_.plain),
      origin,
      suggestions.filter(_.isApplicable)
    )
