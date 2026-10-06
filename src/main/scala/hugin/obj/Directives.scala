package hugin.obj

import hugin.util.*
import hugin.core.*
import scala.collection.mutable

/** Attaches the meta-level call chain and formula-function expansions to diagnostics about generated code. */
object Diag:
  def inItem(span: Span, origin: Origin, expansions: List[Expansion])(d: Diagnostic): Diagnostic =
    val ps = d.primarySpan
    val exp = expansions.filter(e => e.body.exists && ps.exists && ps.source == e.body.source &&
      ps.start >= e.body.start && ps.end <= e.body.end && !(ps.start >= span.start && ps.end <= span.end))
    val frames = exp.map(e => TraceFrame(s"in expansion of formula function `${e.fn}`", e.use))
    val withExp = if frames.isEmpty then d else d.copy(origin = Origin(frames ++ d.origin.frames))
    withExp.withOrigin(Origin(withExp.origin.frames ++ origin.frames))
  def rule(r: Rule)(d: Diagnostic): Diagnostic = inItem(r.span, r.origin, r.expansions)(d)
  def query(q: Query)(d: Diagnostic): Diagnostic = inItem(q.span, q.origin, q.expansions)(d)

/** Phase: attach directives to relations (Figure 2, `dir`), and run deferred signature requirement checks. */
final class DirectivesPhase extends Phase:
  def phaseName = "directives"
  def description = "attach modes, termination, completeness and I/O directives to relations"
  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val ruleNames = p.rules.flatMap(_.name).toSet
    for d <- p.directives do
      def err(msg: String, label: String = "") =
        ctx.report(Diagnostic.error("E0701", msg, d.span, label).withOrigin(d.origin))
      d.target match
        case Some(RelRef.Sym(r)) =>
          d.kind match
            case DirKind.ModeD(spec) =>
              if spec.inputs.length != r.arity then
                err(s"mode for `${r.name}` has ${spec.inputs.length} items but the relation has ${r.arity} columns")
              else
                var ok = true
                for ((_, lbl, sp), i) <- spec.inputs.zipWithIndex; l <- lbl do
                  if !r.cols(i).label.contains(l) then
                    ok = false
                    ctx.report(Diagnostic.error("E0701", s"mode item names label `$l`, but column ${i + 1} of `${r.name}` is ${r.cols(i).label.map(x => s"labelled `$x`").getOrElse("unlabelled")}", sp)
                      .withOrigin(d.origin))
                if ok then
                  val m = Mode(spec.inputs.map(_._1).toVector)
                  if !r.modes.exists(_._1 == m) then r.modes = r.modes :+ (m, d.span)
            case DirKind.TerminatesVar(v, args) =>
              val pos = args.zipWithIndex.collect { case (Term.Var(`v`), i) => i }
              if args.length != r.arity then err(s"`%terminates` pattern has ${args.length} arguments but `${r.name}` has ${r.arity} columns")
              else if pos.length != 1 then err(s"variable `$v` must occur exactly once in the pattern", "ambiguous position")
              else r.terminates = Some((pos.head, d.span))
            case DirKind.TerminatesLabel(l) =>
              r.labelIndex(l) match
                case Some(i) => r.terminates = Some((i, d.span))
                case None => err(s"`${r.name}` has no column labelled `$l`")
            case DirKind.Partial => r.isPartial = true
            case DirKind.Open => r.isOpen = true
            case DirKind.Input => r.isInput = true
            case DirKind.Output => r.isOutput = true
            case DirKind.Derivations => r.derivations = true
            case DirKind.NameHint(v) => r.nameHint = Some(v)
        case _ =>
          d.kind match
            case DirKind.Derivations =>
              d.rule.foreach { rn =>
                if ruleNames.exists(n => n == rn || n.startsWith(rn + "[")) then ctx.unit.derivationRules += rn
                else
                  ctx.report(Diagnostic.error("E0701", s"no rule named `@$rn`", d.span, "unknown rule").withOrigin(d.origin))
              }
            case _ =>
    ctx.unit.deferred.foreach(_())
    ctx.unit.deferred.clear()
  override def show(using Context): String =
    val p = ctx.unit.prog.nn
    p.rels.filter(r => r.modes.nonEmpty || r.terminates.isDefined || r.isOpen || r.isPartial || r.isInput || r.isOutput || r.derivations)
      .map { r =>
        val parts = r.modes.map(m => s"mode ${m._1.show}") ++ r.terminates.map(t => s"terminates ${t._1 + 1}") ++
          (if r.isOpen then List("open") else Nil) ++ (if r.isPartial then List("partial") else Nil) ++
          (if r.isInput then List("input") else Nil) ++ (if r.isOutput then List("output") else Nil) ++
          (if r.derivations then List("derivations") else Nil)
        s"${r.name}: ${parts.mkString(", ")}"
      }.mkString("\n")
