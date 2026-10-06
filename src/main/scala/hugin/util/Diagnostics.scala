package hugin.util

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

/** A structured diagnostic in the style of rustc. */
final case class Diagnostic(
    severity: Severity,
    code: Option[String],
    message: String,
    labels: List[Label] = Nil,
    notes: List[String] = Nil,
    helps: List[String] = Nil,
    origin: Origin = Origin.Source
):
  def primarySpan: Span = labels.find(_.primary).map(_.span).getOrElse(Span.NoSpan)
  def withLabel(span: Span, msg: String = ""): Diagnostic = copy(labels = labels :+ Label(span, msg, primary = false))
  def withPrimary(span: Span, msg: String = ""): Diagnostic = copy(labels = Label(span, msg, primary = true) :: labels)
  def withNote(n: String): Diagnostic = copy(notes = notes :+ n)
  def withHelp(h: String): Diagnostic = copy(helps = helps :+ h)
  def withOrigin(o: Origin): Diagnostic = if o.isEmpty then this else copy(origin = o)

object Diagnostic:
  def error(code: String, msg: String, span: Span, label: String = ""): Diagnostic =
    Diagnostic(Severity.Error, Some(code), msg, List(Label(span, label, primary = true)))
  def warning(code: String, msg: String, span: Span, label: String = ""): Diagnostic =
    Diagnostic(Severity.Warning, Some(code), msg, List(Label(span, label, primary = true)))

/** Collects diagnostics; compilation continues after errors. */
final class Reporter(val maxErrors: Int = 200):
  private val buf = mutable.ArrayBuffer.empty[Diagnostic]
  private val seen = mutable.HashSet.empty[(Option[String], String, Int, Int, String)]
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

  def errorCount: Int = errors
  def warningCount: Int = warnings
  def hasErrors: Boolean = errors > 0
  def diagnostics: List[Diagnostic] = buf.toList

  def sorted: List[Diagnostic] =
    buf.toList.zipWithIndex.sortBy { (d, i) =>
      val s = d.primarySpan
      (s.source.path, s.start, i)
    }.map(_._1)

/** Renders diagnostics in a rustc-like layout. */
final class DiagnosticRenderer(color: Boolean):
  private def c(code: String, s: String): String = if color then s"\u001b[${code}m$s\u001b[0m" else s
  private def bold(s: String) = c("1", s)
  private def sevColor(sev: Severity, s: String) = sev match
    case Severity.Error => c("1;31", s)
    case Severity.Warning => c("1;33", s)
    case Severity.Note => c("1;36", s)
  private def blue(s: String) = c("1;34", s)

  def render(d: Diagnostic): String =
    val sb = new StringBuilder
    val head = d.severity.label + d.code.map(c => s"[$c]").getOrElse("")
    sb ++= sevColor(d.severity, head) ++= bold(s": ${d.message}") += '\n'
    val labels = d.labels.filter(_.span.exists)
    val gutterWidth =
      (labels.map(_.span.startLine + 1) ++ d.origin.frames.filter(_.span.exists).map(_.span.startLine + 1))
        .maxOption.getOrElse(1).toString.length
    val pad = " " * gutterWidth
    renderSnippet(sb, labels, pad, d.severity)
    if d.notes.nonEmpty || d.helps.nonEmpty then
      if labels.isEmpty then () else sb ++= s"$pad ${blue("|")}\n"
      for n <- d.notes do sb ++= s"$pad ${blue("=")} ${bold("note")}: ${indentCont(n, gutterWidth + 9)}\n"
      for h <- d.helps do sb ++= s"$pad ${blue("=")} ${bold("help")}: ${indentCont(h, gutterWidth + 9)}\n"
    for f <- d.origin.frames do
      sb ++= sevColor(Severity.Note, "note") ++= bold(s": ${f.description}") += '\n'
      if f.span.exists then renderSnippet(sb, List(Label(f.span, "", primary = true)), pad, Severity.Note)
    sb.toString

  private def indentCont(s: String, n: Int): String = s.replace("\n", "\n" + " " * n)

  private def renderSnippet(sb: StringBuilder, labels: List[Label], pad: String, sev: Severity): Unit =
    if labels.isEmpty then return
    val primary = labels.find(_.primary).getOrElse(labels.head)
    sb ++= s"$pad${blue("-->")} ${primary.span.show}\n"
    sb ++= s"$pad ${blue("|")}\n"
    // group labels by file+line (other files are rendered with their own header)
    val (same, other) = labels.partition(_.span.source eq primary.span.source)
    val byLine = same.groupBy(_.span.startLine).toList.sortBy(_._1)
    var prevLine = -1
    for (line, ls) <- byLine do
      if prevLine >= 0 && line > prevLine + 1 then sb ++= s"${blue("...")}\n"
      prevLine = line
      val src = ls.head.span.source
      val text = src.lineText(line).replace("\t", " ")
      val num = (line + 1).toString
      sb ++= blue(" " * (pad.length - num.length) + num + " |") ++= s" $text\n"
      // one underline row per label, rightmost first so messages do not collide
      for l <- ls.sortBy(-_.span.startCol) do
        val startCol = l.span.startCol
        val endOff = l.span.end.min(src.lineStart(line) + src.lineText(line).length)
        val endCol = if l.span.endLineDiffers then text.length else src.columnOf(endOff)
        val width = (endCol - startCol).max(1)
        val mark = if l.primary then "^" else "-"
        val u = " " * startCol + (mark * width)
        val msg = if l.message.nonEmpty then " " + l.message else ""
        val styled =
          if l.primary then sevColor(sev, u + msg)
          else blue(u + msg)
        sb ++= s"$pad ${blue("|")} $styled\n"
    for l <- other do
      sb ++= s"$pad${blue("::>")} ${l.span.show}${if l.message.nonEmpty then ": " + l.message else ""}\n"

  def summary(r: Reporter): String =
    val parts = List(
      if r.errorCount > 0 then Some(s"${r.errorCount} error${if r.errorCount == 1 then "" else "s"}") else None,
      if r.warningCount > 0 then Some(s"${r.warningCount} warning${if r.warningCount == 1 then "" else "s"}") else None
    ).flatten
    if parts.isEmpty then "" else parts.mkString(", ") + " found"

extension (s: Span)
  private[util] def endLineDiffers: Boolean = s.source.lineOf(s.end.max(s.start)) != s.startLine && s.end > s.start + 0 &&
    s.source.lineOf((s.end - 1).max(s.start)) != s.startLine
