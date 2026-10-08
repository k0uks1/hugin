package hugin.obj
package check

import hugin.compiler.*

/** Phase: termination check (Section 10; reference: object/termination; docs/NOTES.md, "Termination").
 *
 *  A recursive component with a constructive rule (Definition 10.1) needs one of
 *  the two directions of the size-change criterion:
 *
 *  - (A) descent along derivations ([[SizeChange]]): every cycle of derivation steps makes an argument
 *    strictly smaller from premise to conclusion (or strictly larger below a bound);
 *  - (B) guarded induction: a measure — a tuple of argument positions per relation, compared
 *    lexicographically, integers by `<` and terms by the proper-subterm relation — decreases from the
 *    head to every recursive call, and the head's measure lies in a finite set (bound by a guard atom
 *    outside the component, or by intervals).
 *
 *  `%terminates` names the measure of (B) as a checked hint; without it (A) is tried first, then (B) with
 *  an inferred measure. Decreases and bounds are derived by interval reasoning over the linear
 *  (in)equalities of the body (see [[Arithmetic]]). */
final class TerminationPhase extends Phase:
  def phaseName = "termination"

  def description = "every growing component terminates by descent along derivations or guarded induction (Section 10)"

  def run(using Context): Unit =
    for (comp, verdict) <- Termination.verdicts(ctx.unit) do
      val names = Termination.showComponent(comp)
      def explain(s: String): Unit = if ctx.settings.explainTermination then ctx.unit.explanations += s
      verdict match
        case Verdict.Finite =>
          explain(s"termination: $names: finite: recursive, but no rule is constructive (no numbers, no new terms beyond a finite set)")
        case Verdict.Accepted(how, lines) => explain((s"termination: $names: $how" :: lines).mkString("\n"))
        case Verdict.Rejected(rejection) =>
          val e = rejection.error
          val why = if e.code == hugin.util.diagnostics.Code.E0603 then "no termination argument" else e.message.plain
          explain(s"termination: $names: rejected: $why (${e.code.id})")
          ctx.report(rejection.diagnostic)

/** The outcome of the termination check for one recursive component. */
enum Verdict:
  /** No rule is constructive, so the fixed point is finite. */
  case Finite

  /** A termination argument holds; `how` names it and `lines` explain it (`--explain-termination`). */
  case Accepted(how: String, lines: List[String])
  case Rejected(rejection: Rejection)

object Termination:
  /** The verdict for every recursive component of the unit that is stratified (a cycle through negation or
   *  aggregation is a stratification error, E0601, reported already; it arises e.g. for the demand of an
   *  auxiliary relation of an aggregate, issue #1, B4). */
  def verdicts(unit: CompilationUnit): List[(List[RelSym], Verdict)] =
    val p = unit.prog
    if p == null then return Nil
    given ProgramFacts = unit.facts
    val es = DepGraph.edges(p)
    val compOf = unit.components.zipWithIndex.flatMap((c, i) => c.map(_ -> i)).toMap
    val rulesByComp = p.rules.groupBy(r => headRel(r).flatMap(compOf.get).getOrElse(-1))
    for
      (comp, ci) <- unit.components.zipWithIndex
      inC = comp.toSet
      if comp.length > 1 || es.exists(e => e.from == comp.head && e.to == comp.head)
      if !es.exists(e => e.negative && inC(e.from) && inC(e.to))
    yield
      val rc = RecursiveComponent(unit.facts, comp, rulesByComp.getOrElse(ci, Vector.empty), p.rules, es)
      comp -> verdict(rc, r => unit.splitRules.contains(r))

  /** Checks one recursive component: finite without constructive rules; otherwise a declared measure (a
   *  hint for guarded induction, checked), descent along derivations, or an inferred measure. `split` tells
   *  the split rules of Proposition 8.8. */
  def verdict(rc: RecursiveComponent, split: Rule => Boolean): Verdict =
    val constructiveRules = rc.rules.flatMap(r => Constructive.constructive(r, rc.inC).map(r -> _))
    lazy val declared = rc.comp.flatMap(c => rc.facts(c).terminates.map(t => c -> t._1)).toMap
    lazy val induction = GuardedInduction(rc)
    if constructiveRules.isEmpty then Verdict.Finite
    else if declared.nonEmpty then
      induction.check(declared) match
        case Right(lines) => Verdict.Accepted("terminates, measure declared", lines)
        case Left(f) => Verdict.Rejected(f)
    else
      SizeChange.check(rc.comp, rc.rules) match
        case Right(lines) => Verdict.Accepted("terminates by descent along derivations (A)", lines)
        case Left(descent) =>
          induction.infer match
            case Some((_, lines)) => Verdict.Accepted("terminates, measure inferred", lines)
            case None =>
              val (r, invention) = constructiveRules.head
              Verdict.Rejected(Rejection(noArgument(rc, induction, descent, r, invention, split(r)), Some(r)))

  /** E0603 for the constructive rule `r` of `rc`: the cycle, the fact a split rule asserts, why each
   *  direction fails, and a guard or a relation to measure. */
  private def noArgument(
      rc: RecursiveComponent,
      induction: GuardedInduction,
      descent: SizeChange.Failure,
      r: Rule,
      invention: Invention,
      split: Boolean
  ): TerminationError =
    val head = headRel(r)
    val guard = descent.chain.toList.flatMap(_.steps.flatMap(_.hints)).headOption.map(MissingGuard.of)
    val measurable = rc.comp.find(c => c.kind == RelKind.Plain || DepGraph.isFactCtor(c))
    TerminationError.NoArgument(
      rc.comp,
      invention,
      head.flatMap(rc.cycle),
      if split then head.map(c => (r.heads.head, c)) else None,
      DescentFailure.of(descent),
      induction.inductionFailure,
      guard,
      measurable
    )

  def where(r: Rule): String = s"rule at ${r.span.show}"

  def headRel(r: Rule): Option[RelSym] = r.heads.headOption.collect { case Term.App(RelRef.Sym(c), _) => c }

  def showComponent(comp: List[RelSym]): String = comp.map(_.name).mkString("{", ", ", "}")

  def isInt(t: OType): Boolean = t match
    case OType.Int => true
    case OType.Con(s, _) =>
      s.kind match
        case TypeKind.Refinement(base) => isInt(base)
        case _ => false
    case _ => false

  def plural(n: Int): String = if n == 1 then "1 argument" else s"$n arguments"

  def kind(numeric: Boolean): String = if numeric then "an integer" else "a term"

  def showPositions(c: RelSym, ks: List[Int]): String =
    ks.map(k =>
      s"argument ${k + 1}${c.cols.lift(k).flatMap(_.label).map(l => s" `$l`")
          .getOrElse("")} (${if c.cols.lift(k).exists(col => isInt(col.tpe)) then "integer" else "structural"})"
    )
      .mkString(", ")

  /** A `%terminates` directive for the measure `ks` of `c`. */
  def directive(c: RelSym, ks: List[Int]): String =
    val labels = ks.map(k => c.cols.lift(k).flatMap(_.label))
    if labels.forall(_.isDefined) then s"`%terminates ${hugin.syntax.Printer.measure(labels.flatten)} ${c.name}.`"
    else
      val names = ks.zipWithIndex.map((k, i) => k -> (if ks.length == 1 then "X" else s"X${i + 1}")).toMap
      val pat = (0 until c.arity).map(k => names.getOrElse(k, "_")).mkString(" ")
      s"`%terminates ${hugin.syntax.Printer.measure(ks.map(names))} (${c.name} $pat).`"
