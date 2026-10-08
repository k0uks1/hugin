package hugin.util.diagnostics

import hugin.util.{Diagnostic, Severity}

/** The level of every lint for one run, set on the command line: `-W`, `-A` and `-D` per lint (the last
 *  flag for a lint wins) and `--deny-warnings`, which turns every lint without a flag whose default level
 *  is [[Level.Warning]] into an error (so `-W x --deny-warnings` denies every warning but `x`). Levels apply when diagnostics are shown, never to compilation itself, so changing them does
 *  not recompile (see `compiler.Display`). */
final case class LintLevels(levels: Map[Lint, Level] = Map.empty, denyWarnings: Boolean = false):
  def set(lint: Lint, level: Level): LintLevels = copy(levels = levels.updated(lint, level))

  /** The level of a lint: its flag; or its default, raised by `--deny-warnings`. */
  def level(lint: Lint): Level = levels.getOrElse(lint, implied(lint))

  private def implied(lint: Lint): Level =
    if denyWarnings && lint.defaultLevel == Level.Warning then Level.Error else lint.defaultLevel

  /** The diagnostics as shown at these levels. A lint diagnostic at [[Level.Allow]] is dropped, one at
   *  [[Level.Error]] becomes an error, and each one shown gets a note saying where its level comes from
   *  (which also names the lint, so that users can change its level). Other diagnostics are unchanged. */
  def apply(ds: List[Diagnostic]): List[Diagnostic] = ds.flatMap { d =>
    d.code.lint match
      case None => Some(d)
      case Some(lint) =>
        level(lint) match
          case Level.Allow => None
          case lv => Some(d.copy(severity = lv.severity).withNote(origin(lint, lv)))
  }

  private def origin(lint: Lint, lv: Level): String =
    if levels.contains(lint) then s"`${LintLevels.flag(lv)} ${lint.name}` is set on the command line"
    else if lv != lint.defaultLevel then s"`-D ${lint.name}` is implied by `--deny-warnings`"
    else s"`${LintLevels.flag(lv)} ${lint.name}` is on by default"

object LintLevels:
  /** The command-line flag setting a level. */
  def flag(level: Level): String = level match
    case Level.Error => "-D"
    case Level.Warning => "-W"
    case Level.Allow => "-A"

  /** Whether diagnostics shown at some levels include an error. */
  def hasErrors(shown: List[Diagnostic]): Boolean = shown.exists(_.severity == Severity.Error)
