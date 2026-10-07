package hugin.obj
package check

import hugin.util.*
import hugin.compiler.*

/** Phase: termination check (Section 10; docs/REDESIGN.md §4; docs/NOTES.md, "Termination").
 *
 *  A recursive component with a constructive rule (Definition 10.1) needs a `%partial` relation or one of
 *  the two directions of the size-change criterion:
 *
 *  - (A) descent along derivations ([[SizeChange]]): every cycle of derivation steps makes an argument
 *    strictly smaller from premise to conclusion (or strictly larger below a bound);
 *  - (B) guarded induction: a measure — a tuple of argument positions per relation, compared
 *    lexicographically, integers by `<` and terms by the proper-subterm relation — decreases from the
 *    head to every recursive call, and the head's measure lies in a finite set (bound by a guard atom
 *    outside the component, or by intervals). Moded components are checked on their demands instead.
 *
 *  `%terminates` names the measure of (B) as a checked hint; without it (A) is tried first, then (B) with
 *  an inferred measure. Decreases and bounds are derived by interval reasoning over the linear
 *  (in)equalities of the body (see [[Arithmetic]]). */
final class TerminationPhase extends Phase:
  def phaseName = "termination"

  def description = "every growing component terminates by descent along derivations or guarded induction, or is %partial (Section 10)"

  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val es = DepGraph.edges(p)
    val compOf = ctx.unit.components.zipWithIndex.flatMap((c, i) => c.map(_ -> i)).toMap
    val rulesByComp = p.rules.groupBy(r => Termination.headRel(r).flatMap(compOf.get).getOrElse(-1))
    for (comp, ci) <- ctx.unit.components.zipWithIndex do
      val inC = comp.toSet
      val recursive = comp.length > 1 || es.exists(e => e.from == comp.head && e.to == comp.head)
      // a cycle through negation or aggregation is a stratification error (E0601), reported already;
      // it arises e.g. for the demand of an auxiliary relation of an aggregate (issue #1, B4)
      val stratified = !es.exists(e => e.negative && inC(e.from) && inC(e.to))
      if recursive && stratified then
        checkComponent(RecursiveComponent(ctx.unit.facts, comp, rulesByComp.getOrElse(ci, Vector.empty), p.rules, es))

  /** Checks one recursive component: finite without constructive rules; otherwise `%partial`, a declared
   *  measure (a hint for guarded induction, checked), descent along derivations, or an inferred measure. */
  private def checkComponent(rc: RecursiveComponent)(using Context): Unit =
    val names = Termination.showComponent(rc.comp)
    def explain(s: String): Unit = if ctx.settings.explainTermination then ctx.unit.explanations += s
    def accept(how: String, lines: List[String]): Unit = explain((s"termination: $names: $how" :: lines).mkString("\n"))
    val constructiveRules = rc.rules.flatMap(r => Constructive.constructive(r, rc.inC).map(r -> _))
    val partial = rc.comp.filter(ctx.unit.facts(_).partial)
    // a component of demand relations only is measured by the relations they are demands of
    lazy val declared = rc.comp.map(Termination.base).flatMap(c => ctx.unit.facts(c).terminates.map(t => c -> t._1)).toMap
    lazy val induction = GuardedInduction(rc)
    if constructiveRules.isEmpty then
      explain(s"termination: $names: finite: recursive, but no rule is constructive (no numbers, no new terms beyond a finite set)")
    else if partial.nonEmpty then
      explain(
        s"termination: $names: not checked: ${partial.map(r => s"`${r.name}`").mkString(", ")} is %partial (evaluated with the round budget)"
      )
    else if declared.nonEmpty then
      induction.check(declared) match
        case Right(lines) => accept("terminates, measure declared", lines)
        case Left(f) =>
          explain(s"termination: $names: rejected: ${f.message} (E0604)")
          ctx.report(f.diagnostic)
    else
      SizeChange.check(rc.comp, rc.rules) match
        case Right(lines) => accept("terminates by descent along derivations (A)", lines)
        case Left(descent) =>
          induction.infer match
            case Some((_, lines)) => accept("terminates, measure inferred", lines)
            case None =>
              val (r, (why, sp)) = constructiveRules.head
              explain(s"termination: $names: rejected: no termination argument (E0603)")
              ctx.report(Diag.rule(r)(Failures.noMeasure(rc, induction, descent, r, why, sp)))

object Termination:
  def headRel(r: Rule): Option[RelSym] = r.heads.headOption.collect { case Term.App(RelRef.Sym(c), _) => c }

  /** The relation a demand relation belongs to, or the relation itself. */
  def base(c: RelSym): RelSym = c.kind match
    case RelKind.Demand(of, _) => of
    case _ => c

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
