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
  private def style(attrs: fansi.Attrs, s: String): String = if color then attrs(s).render else s
  private def bold(s: String) = style(fansi.Bold.On, s)
  private def sevColor(sev: Severity, s: String) = sev match
    case Severity.Error => style(fansi.Color.Red ++ fansi.Bold.On, s)
    case Severity.Warning => style(fansi.Color.Yellow ++ fansi.Bold.On, s)
    case Severity.Note => style(fansi.Color.Cyan ++ fansi.Bold.On, s)
  private def blue(s: String) = style(fansi.Color.Blue ++ fansi.Bold.On, s)

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
      // one marker row for all labels of this line; the rightmost label's message goes inline,
      // the others' messages on the rows below
      val lineEnd = src.lineStart(line) + src.lineText(line).length
      val marks = ls.map { l =>
        val startCol = l.span.startCol
        val endCol = if l.span.endLineDiffers then text.length else src.columnOf(l.span.end.min(lineEnd))
        (l, startCol, (endCol - startCol).max(1))
      }.sortBy(_._2)
      val width = marks.map((_, c, w) => c + w).max
      val row = Array.fill(width)(' ')
      val prim = Array.fill(width)(false)
      // secondary first, so primary markers win where they overlap
      for (l, c, w) <- marks.sortBy(_._1.primary); k <- c until c + w do
        row(k) = if l.primary then '^' else '-'
        prim(k) = l.primary
      val styledRow = new StringBuilder
      var k = 0
      while k < width do
        var j = k
        while j < width && prim(j) == prim(k) && (row(j) == ' ') == (row(k) == ' ') do j += 1
        val seg = new String(row, k, j - k)
        styledRow ++= (if row(k) == ' ' then seg else if prim(k) then sevColor(sev, seg) else blue(seg))
        k = j
      val (lastL, _, _) = marks.maxBy((_, c, w) => (c + w, c))
      def styledMsg(l: Label, m: String) = if l.primary then sevColor(sev, m) else blue(m)
      val inline = if lastL.message.nonEmpty then " " + styledMsg(lastL, lastL.message) else ""
      sb ++= s"$pad ${blue("|")} ${styledRow.toString.replaceAll("\\s+$", "")}$inline\n"
      for (l, c, _) <- marks.reverse if (l ne lastL) && l.message.nonEmpty do
        sb ++= s"$pad ${blue("|")} ${" " * c}${styledMsg(l, l.message)}\n"
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
