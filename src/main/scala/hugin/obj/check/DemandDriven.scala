package hugin.obj
package check

import hugin.obj.typing.Moding

/** The demand-driven case of guarded induction for components of `%mode`d relations (checked on their
 *  demands). It exists only for the built-in demand transformation and goes with it (docs/REDESIGN.md
 *  §10, C3). */
final class DemandDriven(rc: RecursiveComponent):
  import Termination.*
  import Decrease.*
  import Failures.*

  private val (comp, rules, allRules, facts) = (rc.comp, rc.rules, rc.allRules, rc.facts)
  private val inC = rc.inC

  /** Demand-driven evaluation: every demand is smaller than the demand guarding it, and integer slots
   *  are bounded below where they decrease. */
  def check(ctx: MeasureCtx): Either[TerminationFailure, List[String]] =
    def demandOf(x: RelSym): Option[RelSym] = x.kind match
      case RelKind.Demand(of, _) if ctx.has(of) => Some(of)
      case _ => None
    // relations and demands of the other groups of the component (their own group checks them)
    def otherGroup(x: RelSym): Boolean = !ctx.has(x) && ctx.measuredAnywhere(x) || (x.kind match
      case RelKind.Demand(of, _) => !ctx.has(of) && ctx.measuredAnywhere(of)
      case _ => false
    )
    val measured = ctx.measures.keys.toList.sortBy(_.name)
    val unmoded = measured.find(!facts.hasModes(_)).map { c =>
      val other = measured.find(facts.hasModes).get
      TerminationFailure(
        s"`${c.name}` has a measure but no `%mode`",
        ctx.directive(c).getOrElse(c.span),
        "measure declared here",
        None,
        None,
        notes = List(s"`${other.name}` in the same component is moded, so the component is evaluated by demand"),
        helps = List(s"declare a mode for `${c.name}`, e.g. `%mode ${c.name} ${Mode(Vector.fill(c.arity)(true)).show}.`")
      )
    }
    val notInput = measured.iterator.flatMap(c =>
      facts.modes(c).iterator.flatMap((m, sp) => ctx.of(c).find(k => !m.inputs.lift(k).contains(true)).map(k => (c, m, sp, k)))
    ).nextOption().map { (c, m, sp, k) =>
      TerminationFailure(
        s"invalid `%terminates` directive for `${c.name}`",
        sp,
        s"argument ${k + 1} is not an input of mode ${m.show}",
        None,
        ctx.directive(c),
        notes = List("in a moded component the measure is checked on the demands, which consist of the input arguments")
      )
    }
    unmoded.orElse(notInput).orElse(
      rc.unmeasuredConstructive(ctx, h => ctx.has(h) || demandOf(h).isDefined || otherGroup(h), answers = true)
    ).toLeft(()).flatMap {
      _ =>
        val lines = List.newBuilder[String]
        lines += "  demand-driven: each demand is smaller than the demand guarding it; decreasing integers are bounded below"
        // Rules of measured relations may call unmeasured relations of the component only if those do not
        // read answers of measured relations (except through demands): their facts are then determined by
        // the demands. Otherwise answers could feed themselves without any demand (`d X Z :- c X Z`).
        val calls = rules.iterator.filter(r => headRel(r).exists(ctx.has)).flatMap { r =>
          r.body.collectFirst(Function.unlift {
            case a @ Formula.Atom(RelRef.Sym(d), _, _) if inC(d) && !ctx.has(d) && demandOf(d).isEmpty && !otherGroup(d) =>
              rc.readsAnswers(d, ctx.measuredAnywhere, x => demandOf(x).isDefined || otherGroup(x))
                .map(m => unmeasuredCall(ctx, r, headRel(r).get, a, d, Some(m)))
            case _ => None
          })
        }.nextOption()
        // Demand rules guarded by a demand of a measured relation, wherever they are (the demands of a
        // relation may form a component of their own, `log2^d H :- log2^d N, H = N / 2`), and the
        // demand rules of this component that read it (whose guard must then be measured).
        def guardOf(r: Rule) = r.body.collectFirst { case Formula.Atom(RelRef.Sym(x), _, _) if x.isDemand => x }
        def isDemandRule(r: Rule) = headRel(r).exists(h => demandOf(h).isDefined)
        val demandRules = (rules.filter(r =>
          isDemandRule(r) && r.body.exists {
            case Formula.Atom(RelRef.Sym(x), _, _) => inC(x)
            case _ => false
          }
        ) ++ allRules.filter(r => isDemandRule(r) && guardOf(r).exists(g => demandOf(g).isDefined))).distinct
        // A seed of the component: a demand rule without guard, or guarded by a demand of a relation
        // outside the component, that reads the component. The moded relation is then called from a rule
        // whose prefix reads relations depending on its answers (`d0 X :- e L X, len L N` and
        // `d2 N :- d0 X, f L X, len L N`). Its demands are finitely many if every input comes from a
        // finite set, independently of the component's facts.
        lazy val finiteCols = rc.finiteColumns(ctx.measuredAnywhere)
        def seed(r: Rule, us: List[Term], e: RelSym): Option[TerminationFailure] =
          val finite = rc.finiteSources(r.body, finiteCols)
          us.find(u => !Moding.vars(u).subsetOf(finite)) match
            case None =>
              lines += s"  ${where(r)}: demand `${ObjPrinter.term(r.heads.head)}` from outside the component: its inputs take finitely many values"
              None
            case Some(u) =>
              Some(TerminationFailure(
                s"invalid `%terminates` directive for `${e.name}`",
                u.span,
                s"the demanded `${ObjPrinter.term(u)}` may take infinitely many values",
                Some(r),
                ctx.directive(e),
                notes = List(
                  s"this call demands `${e.name}` with values read from relations that depend on the answers of `${e.name}`, so the demands could grow without bound"
                ),
                helps = List(s"bind the argument by a relation that does not depend on the answers of `${e.name}`", partialHelp(e))
              ))
        val demands = demandRules.iterator.flatMap { r =>
          val Term.App(RelRef.Sym(dh), us) = r.heads.head: @unchecked
          val e = demandOf(dh).get
          val guard = r.body.collectFirst { case g @ Formula.Atom(RelRef.Sym(x), _, _) if x.isDemand => g }
          guard match
            case Some(Formula.Atom(RelRef.Sym(dg), _, _)) if !inC(dg) && demandOf(dg).isEmpty && !otherGroup(dg) => seed(r, us, e)
            case Some(g @ Formula.Atom(RelRef.Sym(dg), ws, _)) =>
              demandOf(dg) match
                case None if otherGroup(dg) => None // a call between groups: ordered by the demand graph
                case None =>
                  val gOf = dg.kind match
                    case RelKind.Demand(of, _) => of
                    case _ => dg
                  Some(unmeasuredCall(ctx, r, gOf, g, gOf))
                case Some(c) =>
                  val arith = Arithmetic(r.body)
                  val outside = rc.boundOutside(r.body)
                  val (ki, kg) = (inputPositions(dh, e, ctx.of(e)), inputPositions(dg, c, ctx.of(c)))
                  val small = ki.map(us)
                  val big = kg.map(ws)
                  compare(ctx.slots, big, small, arith, r.body) match
                    case Left(f) =>
                      Some(decreaseFailure(ctx, r, c, e, r.heads.head.span, big, small, f, "the call", "the caller"))
                    case Right((i, why)) =>
                      val u = small(i)
                      val lower =
                        if !ctx.slots(i) then Some("")
                        else if Moding.vars(u).subsetOf(outside) then
                          Some(s"; `${ObjPrinter.term(u)}` is bound by relations outside the component")
                        else arith(u).lo.map(b => s"; `${ObjPrinter.term(u)}` >= $b")
                      lower match
                        case Some(l) =>
                          lines += s"  ${where(r)}: demand for `${ObjPrinter.term(r.heads.head)}` from `${ObjPrinter.formula(g)}`: $why$l"
                          None
                        case None => Some(lowerBoundFailure(ctx, r, e, r.heads.head.span, i, u))
            case _ => seed(r, us, e)
        }.nextOption()
        calls.orElse(demands).toLeft(lines.result())
    }

  /** The positions of the measured arguments among the inputs of a demand relation. */
  def inputPositions(d: RelSym, c: RelSym, ks: List[Int]): List[Int] = d.kind match
    case RelKind.Demand(_, m) => ks.map(k => m.inputs.take(k).count(identity))
    case _ => ks
