package hugin.obj
package typing

import hugin.util.*
import hugin.compiler.*

/** Phase: attach directives to relations (Figure 2, `dir`), and check the signature requirements recorded by
 *  the meta evaluator ([[RequirementCheck]]). */
final class DirectivesPhase extends Phase:
  def phaseName = "directives"
  def description = "attach modes, termination, completeness and I/O directives to relations"
  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val ruleNames = p.rules.flatMap(_.name).toSet
    var facts = ProgramFacts.empty
    def set(r: RelSym)(f: RelDirectives => RelDirectives): Unit = facts = facts.updated(r)(f)
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
                    ctx.report(Diagnostic.error(
                      "E0701",
                      s"mode item names label `$l`, but column ${i + 1} of `${r.name}` is ${r.cols(i).label.map(x => s"labelled `$x`").getOrElse("unlabelled")}",
                      sp
                    )
                      .withOrigin(d.origin))
                if ok then
                  val m = Mode(spec.inputs.map(_._1).toVector)
                  if !facts.modes(r).exists(_._1 == m) then set(r)(x => x.copy(modes = x.modes :+ (m, d.span)))
            case DirKind.TerminatesVar(vs, args) =>
              def pos(v: String) = args.zipWithIndex.collect { case (Term.Var(`v`), i) => i }
              if args.length != r.arity then
                err(s"`%terminates` pattern has ${args.length} arguments but `${r.name}` has ${r.arity} columns")
              else
                (vs.diff(vs.distinct).headOption, vs.find(pos(_).length != 1)) match
                  case (Some(v), _) => err(s"variable `$v` occurs twice in the measure", "ambiguous position")
                  case (_, Some(v)) => err(s"variable `$v` must occur exactly once in the pattern", "ambiguous position")
                  case _ => set(r)(_.copy(terminates = Some((vs.map(pos(_).head), d.span))))
            case DirKind.TerminatesLabel(ls) =>
              ls.find(r.labelIndex(_).isEmpty) match
                case Some(l) => err(s"`${r.name}` has no column labelled `$l`")
                case None if ls.distinct.length != ls.length =>
                  err(s"label `${ls.diff(ls.distinct).head}` occurs twice in the measure", "ambiguous position")
                case None => set(r)(_.copy(terminates = Some((ls.flatMap(r.labelIndex), d.span))))
            case DirKind.Open => set(r)(_.copy(open = true))
            case DirKind.Input => set(r)(_.copy(input = true))
            case DirKind.Output => set(r)(_.copy(output = true))
            case DirKind.Derivations => set(r)(_.copy(derivations = true))
            case DirKind.NameHint(v) => set(r)(_.copy(nameHint = Some(v)))
        case _ =>
          d.kind match
            case DirKind.Derivations =>
              d.rule.foreach { rn =>
                if ruleNames.exists(n => n == rn || n.startsWith(rn + "[")) then ctx.unit.derivationRules += rn
                else
                  ctx.report(Diagnostic.error("E0701", s"no rule named `@$rn`", d.span, "unknown rule").withOrigin(d.origin))
              }
            case _ =>
    ctx.unit.facts = facts
    ctx.unit.requirements.foreach(checkRequirement)

  /** E0208: a relation passed to a functor does not satisfy a requirement of the parameter's signature. */
  private def checkRequirement(c: RequirementCheck)(using Context): Unit =
    val rel = c.rel
    val dirs = ctx.unit.facts(rel)
    val failure = c.requirement match
      case Requirement.Complete(label, _) =>
        Option.when(dirs.open)(
          Diagnostic.error(
            "E0208",
            s"relation `${rel.name}` does not satisfy `%complete $label`",
            c.use,
            s"`${rel.name}` is open"
          ).withNote("the functor negates or aggregates over this relation, which needs complete knowledge")
        )
      case Requirement.HasMode(label, mode, _) =>
        Option.when(!dirs.modes.exists(_._1 == mode)) {
          val directive = s"%mode ${rel.name} ${mode.inputs.map(b => if b then "+" else "-").mkString(" ")}."
          directiveBefore(
            Diagnostic.error("E0208", s"relation `${rel.name}` does not have mode `${mode.show}`", c.use, s"required for field `$label`")
              .withHelp(s"declare `$directive`"),
            rel,
            directive
          )
        }
    failure.foreach(d => ctx.report(d.withLabel(c.requirement.span, "required here").withOrigin(c.origin)))

  /** Suggests inserting a directive on its own line before the declaration of `rel`, if the declaration
   *  names it as written (not a relation of a module body, whose name has a prefix). */
  private def directiveBefore(d: Diagnostic, rel: RelSym, directive: String): Diagnostic =
    val decl = rel.span
    val text = decl.text
    val namesIt =
      text.startsWith(rel.name) && !text.drop(rel.name.length).headOption.exists(c => c.isLetterOrDigit || c == '_' || c == '\'')
    if !decl.exists || !namesIt then d
    else
      val src = decl.source
      val indent = src.content.substring(src.lineStart(decl.startLine), decl.start)
      d.withSuggestion(s"declare `$directive`", Span(src, decl.start, decl.start), s"$directive\n${if indent.isBlank then indent else ""}")
  override def show(using Context): String =
    val p = ctx.unit.prog.nn
    val facts = ctx.unit.facts
    p.rels.map(r => (r, facts(r))).filter((_, d) => d.copy(nameHint = None) != RelDirectives.none)
      .map { (r, d) =>
        val terminates = d.terminates.map(t => s"terminates ${hugin.syntax.Printer.measure(t._1.map(k => (k + 1).toString))}")
        val parts = d.modes.map(m => s"mode ${m._1.show}") ++ terminates ++
          (if d.open then List("open") else Nil) ++
          (if d.input then List("input") else Nil) ++ (if d.output then List("output") else Nil) ++
          (if d.derivations then List("derivations") else Nil)
        s"${r.name}: ${parts.mkString(", ")}"
      }.mkString("\n")
