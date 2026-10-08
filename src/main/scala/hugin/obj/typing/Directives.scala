package hugin.obj
package typing

import hugin.util.*
import hugin.compiler.*

/** Phase: attach directives to relations (Figure 2, `dir`), and check the signature requirements recorded by
 *  the meta evaluator ([[RequirementCheck]]). */
final class DirectivesPhase extends Phase:
  def phaseName = "directives"
  def description = "attach termination, completeness and I/O directives to relations"
  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val ruleNames = p.rules.flatMap(_.name).toSet
    var facts = ProgramFacts.empty
    def set(r: RelSym)(f: RelDirectives => RelDirectives): Unit = facts = facts.updated(r)(f)
    for d <- p.directives do
      d.target match
        case Some(RelRef.Sym(r)) =>
          d.kind match
            case DirKind.TerminatesVar(vs, args) =>
              def pos(v: String) = args.zipWithIndex.collect { case (Term.Var(`v`), i) => i }
              if args.length != r.arity then
                ctx.report(DirectiveError.TerminatesArity(r, args.length, d.span, d.origin))
              else
                (vs.diff(vs.distinct).headOption, vs.find(pos(_).length != 1)) match
                  case (Some(v), _) => ctx.report(DirectiveError.MeasureVariableTwice(v, d.span, d.origin))
                  case (_, Some(v)) => ctx.report(DirectiveError.MeasureVariableNotOnce(v, d.span, d.origin))
                  case _ => set(r)(_.copy(terminates = Some((vs.map(pos(_).head), d.span))))
            case DirKind.TerminatesLabel(ls) =>
              ls.find(r.labelIndex(_).isEmpty) match
                case Some(l) => ctx.report(DirectiveError.MeasureUnknownLabel(r, l, d.span, d.origin))
                case None if ls.distinct.length != ls.length =>
                  ctx.report(DirectiveError.MeasureLabelTwice(ls.diff(ls.distinct).head, d.span, d.origin))
                case None => set(r)(_.copy(terminates = Some((ls.flatMap(r.labelIndex), d.span))))
            case DirKind.Open => set(r)(_.copy(open = true))
            case DirKind.Input => set(r)(_.copy(input = true))
            case DirKind.Output => set(r)(_.copy(output = true))
            case DirKind.Derivations => set(r)(_.copy(derivations = true))
        case _ =>
          d.kind match
            case DirKind.Derivations =>
              d.rule.foreach { rn =>
                if ruleNames.exists(n => n == rn || n.startsWith(rn + "[")) then ctx.unit.derivationRules += rn
                else
                  ctx.report(DirectiveError.UnknownRule(rn, d.span, d.origin))
              }
            case _ =>
    ctx.unit.facts = facts
    ctx.unit.requirements.foreach(checkRequirement)

  /** E0208: a relation passed to a functor does not satisfy a requirement of the parameter's signature. */
  private def checkRequirement(c: RequirementCheck)(using Context): Unit =
    val rel = c.rel
    val dirs = ctx.unit.facts(rel)
    c.requirement match
      case Requirement.Complete(label, _) =>
        if dirs.open then ctx.report(RequirementError.NotComplete(rel, label, c.use, c.requirement.span, c.origin))

  override def show(using Context): String =
    val p = ctx.unit.prog.nn
    val facts = ctx.unit.facts
    p.rels.map(r => (r, facts(r))).filter((_, d) => d != RelDirectives.none)
      .map { (r, d) =>
        val terminates = d.terminates.map(t => s"terminates ${hugin.syntax.Printer.measure(t._1.map(k => (k + 1).toString))}")
        val parts = terminates.toList ++
          (if d.open then List("open") else Nil) ++
          (if d.input then List("input") else Nil) ++ (if d.output then List("output") else Nil) ++
          (if d.derivations then List("derivations") else Nil)
        s"${r.name}: ${parts.mkString(", ")}"
      }.mkString("\n")
