package hugin.util

/** Renders diagnostics in a rustc-like layout. Suggestions are not shown as patched source lines: each
 *  one is described by a help, and editors apply them as quick fixes. */
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
    val head = d.severity.label + d.code.map(c => s"[${c.id}]").getOrElse("")
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
