package hugin.obj

import hugin.util.*

/** Attaches the meta-level call chain and formula-function expansions to diagnostics about generated code. */
object Diag:
  def inItem(span: Span, origin: Origin, expansions: List[Expansion])(d: Diagnostic): Diagnostic =
    val ps = d.primarySpan
    val exp = expansions.filter(e =>
      e.body.exists && ps.exists && ps.source == e.body.source &&
        ps.start >= e.body.start && ps.end <= e.body.end && !(ps.start >= span.start && ps.end <= span.end)
    )
    val frames = exp.map(e => TraceFrame(s"in expansion of formula function `${e.fn}`", e.use))
    val withExp = if frames.isEmpty then d else d.copy(origin = Origin(frames ++ d.origin.frames))
    withExp.withOrigin(Origin(withExp.origin.frames ++ origin.frames))
  def rule(r: Rule)(d: Diagnostic): Diagnostic = inItem(r.span, r.origin, r.expansions)(d)
  def query(q: Query)(d: Diagnostic): Diagnostic = inItem(q.span, q.origin, q.expansions)(d)
