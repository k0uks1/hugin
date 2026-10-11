package hugin.util

import hugin.util.diagnostics.{Applicability, Code, Edit, Problem, Suggestion}
import scala.collection.mutable

enum Severity:
  case Error, Warning, Note
  def label: String = this match
    case Error => "error"
    case Warning => "warning"
    case Note => "note"

final case class Label(span: Span, message: String, primary: Boolean)

/** One frame of the meta-level expansion chain that produced a piece of object code. */
final case class TraceFrame(description: String, span: Span)

/** Where a piece of (possibly generated) object code came from: the innermost frame first. */
final case class Origin(frames: List[TraceFrame]):
  def push(f: TraceFrame): Origin = Origin(f :: frames)
  def isEmpty: Boolean = frames.isEmpty

object Origin:
  val Source: Origin = Origin(Nil)

/** A structured diagnostic in the style of rustc: plain data (strings, spans and a [[Code]]), as stored by
 *  the query database and consumed by the renderers and the LSP. Phases build it from a typed [[Problem]]
 *  (`Problem.toDiagnostic`). `suggestions` are edits with an applicability, the most likely one first;
 *  each one comes with a help that describes it in prose. Every diagnostic has a code, also the messages
 *  of the tools (the REPL, the language server: [[Code.E1101]], [[Code.E1102]]). */
final case class Diagnostic(
    severity: Severity,
    code: Code,
    message: String,
    labels: List[Label] = Nil,
    notes: List[String] = Nil,
    helps: List[String] = Nil,
    origin: Origin = Origin.Source,
    suggestions: List[Suggestion] = Nil
):
  def primarySpan: Span = labels.find(_.primary).map(_.span).getOrElse(Span.NoSpan)

  /** The diagnostic with every span replaced by `f` (labels, suggestions, the expansion chain). */
  def mapSpans(f: Span => Span): Diagnostic =
    def g(sp: Span) = if sp.exists then f(sp) else sp
    copy(
      labels = labels.map(l => l.copy(span = g(l.span))),
      origin = Origin(origin.frames.map(fr => fr.copy(span = g(fr.span)))),
      suggestions = suggestions.map(_.mapSpans(g))
    )
  def withLabel(span: Span, msg: String = ""): Diagnostic = copy(labels = labels :+ Label(span, msg, primary = false))
  def withPrimary(span: Span, msg: String = ""): Diagnostic = copy(labels = Label(span, msg, primary = true) :: labels)
  def withNote(n: String): Diagnostic = copy(notes = notes :+ n)
  def withHelp(h: String): Diagnostic = copy(helps = helps :+ h)
  def withOrigin(o: Origin): Diagnostic = if o.isEmpty then this else copy(origin = o)

  /** Adds a suggested edit, if its span is real (generated code has no text to edit). */
  def withSuggestion(message: String, span: Span, replacement: String, applicability: Applicability): Diagnostic =
    val s = Suggestion(message, List(Edit(span, replacement)), applicability)
    if s.isApplicable then copy(suggestions = suggestions :+ s) else this

object Diagnostic:
  /** The diagnostic of a problem (see [[Problem.toDiagnostic]]). */
  def of(p: Problem): Diagnostic = p.toDiagnostic

/** Collects diagnostics; compilation continues after errors. */
final class Reporter(val maxErrors: Int = 200):
  private val buf = mutable.ArrayBuffer.empty[Diagnostic]
  private val seen = mutable.HashSet.empty[(Code, String, Int, Int, String)]
  private var errors = 0
  private var warnings = 0

  def report(d: Diagnostic): Unit =
    val key = (d.code, d.message, d.primarySpan.start, d.primarySpan.end, d.primarySpan.source.path)
    if seen.add(key) then
      d.severity match
        case Severity.Error => errors += 1
        case Severity.Warning => warnings += 1
        case _ =>
      buf += d

  def report(p: Problem): Unit = report(p.toDiagnostic)

  /** The position in the reported diagnostics, for [[discardSince]]. */
  def mark: Int = buf.length

  /** Drops the diagnostics reported since `mark` (those of a speculative attempt). */
  def discardSince(mark: Int): Unit =
    while buf.length > mark do
      val d = buf.remove(buf.length - 1)
      seen -= ((d.code, d.message, d.primarySpan.start, d.primarySpan.end, d.primarySpan.source.path))
      d.severity match
        case Severity.Error => errors -= 1
        case Severity.Warning => warnings -= 1
        case _ =>

  def errorCount: Int = errors
  def warningCount: Int = warnings
  def hasErrors: Boolean = errors > 0
  def diagnostics: List[Diagnostic] = buf.toList

  def sorted: List[Diagnostic] =
    buf.toList.zipWithIndex.sortBy { (d, i) =>
      val s = d.primarySpan
      (s.source.path, s.start, i)
    }.map(_._1)
