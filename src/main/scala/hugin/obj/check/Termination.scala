package hugin.obj
package check

import hugin.util.*
import hugin.compiler.*

import hugin.obj.typing.Moding

/** Phase: termination check (Section 10). */
final class TerminationPhase extends Phase:
  def phaseName = "termination"
  def description = "every growing component has a valid %terminates directive or is %partial (Section 10)"

  /** Why a rule is constructive (Definition 10.1), if it is. */
  def constructive(r: Rule): Option[(String, Span)] =
    DepGraph.newHeadConstructors(r).headOption.map(t =>
      (s"its head constructs `${ObjPrinter.term(t)}`, which is not matched in the body", t.span)
    )
      .orElse {
        val asVars = r.body.collect { case Formula.Atom(_, _, Some(v)) => v }.toSet
        val headVars = r.heads.flatMap(Moding.vars).toSet
        asVars.intersect(headVars).headOption.map(v => (s"the matched fact `${Var.display(v)}` is lifted into the head", r.span))
      }
      .orElse {
        def arith(t: Term): Option[Term] = t match
          case a: Term.Arith => Some(a)
          case n: Term.Neg => Some(n)
          case Term.App(_, as) => as.flatMap(arith).headOption
          case Term.As(x, _) => arith(x)
          case Term.Ascr(x, _) => arith(x)
          case _ => None
        r.heads.flatMap(arith).headOption.map(t => (s"its head computes `${ObjPrinter.term(t)}`", t.span))
      }
      .orElse {
        val headVars = r.heads.flatMap(Moding.vars).toSet
        r.body.collectFirst {
          case c @ Formula.Cmp(CmpOp.Eq, Term.Var(x), e) if headVars(x) && hasOp(e) =>
            (s"head variable `$x` is computed by `${ObjPrinter.formula(c)}`", c.span)
          case c @ Formula.Cmp(CmpOp.Eq, e, Term.Var(x)) if headVars(x) && hasOp(e) =>
            (s"head variable `$x` is computed by `${ObjPrinter.formula(c)}`", c.span)
        }
      }

  private def hasOp(t: Term): Boolean = t match
    case _: Term.Arith | _: Term.Neg => true
    case Term.App(_, as) => as.exists(hasOp)
    case _ => false

  private def headRel(r: Rule): Option[RelSym] = r.heads.headOption.collect { case Term.App(RelRef.Sym(c), _) => c }

  def run(using Context): Unit =
    val p = ctx.unit.prog
    if p == null then return
    val es = DepGraph.edges(p)
    val compOf = ctx.unit.components.zipWithIndex.flatMap((c, i) => c.map(_ -> i)).toMap
    val rulesByComp = p.rules.groupBy(r => headRel(r).flatMap(compOf.get).getOrElse(-1))
    for (comp, ci) <- ctx.unit.components.zipWithIndex do
      val inC = comp.toSet
      val recursive = comp.length > 1 || es.exists(e => e.from == comp.head && e.to == comp.head)
      val rules = rulesByComp.getOrElse(ci, Vector.empty)
      val constructiveRules = rules.flatMap(r => constructive(r).map(r -> _))
      if recursive && constructiveRules.nonEmpty && !comp.exists(_.isPartial) then
        val candidates = comp.filter(_.terminates.isDefined)
        if candidates.isEmpty then
          val (r, (why, sp)) = constructiveRules.head
          val names = comp.filterNot(c => c.isCtor || c.isDemand).map(_.name)
          ctx.report(Diag.rule(r)(Diagnostic.error("E0603", "growing component without a valid %terminates directive", sp, why)
            .withNote(
              s"the recursive component {${comp.map(_.name).mkString(", ")}} contains this constructive rule, so its fixed point may be infinite"
            )
            .withHelp(names.headOption.map(n =>
              s"declare a structurally decreasing argument, e.g. `%terminates X ($n ...)`, or mark the relation `%partial $n.`"
            ).getOrElse("mark a relation of the component %partial"))))
        else
          val results = candidates.map(c => c -> validate(c, inC, rules))
          if !results.exists(_._2.isEmpty) then
            val (c, Some((msg, sp, rule))) = results.head: @unchecked
            var d = Diagnostic.error("E0604", s"invalid `%terminates` directive for `${c.name}`", sp, msg)
            d = d.withLabel(c.terminates.get._2, "directive declared here")
            ctx.report(rule.map(r => Diag.rule(r)(d)).getOrElse(d))

  /** Checks Definition 10.3; returns the first violation. */
  private def validate(c: RelSym, inC: Set[RelSym], rules: Vector[Rule]): Option[(String, Span, Option[Rule])] =
    val k = c.terminates.get._1
    def isDemandOf(r: RelSym) = r.kind match
      case RelKind.Demand(of, _) => of == c
      case _ => false
    // every rule of C whose head is neither c nor a demand relation of c is non-constructive
    rules.find(r => headRel(r).exists(h => h != c && !isDemandOf(h)) && constructive(r).isDefined).map { r =>
      (
        s"another constructive relation in the component: `${headRel(r).get.name}` (${constructive(r).get._1})",
        constructive(r).get._2,
        Some(r)
      )
    }.orElse {
      val numeric = c.cols.lift(k).exists(col =>
        col.tpe == OType.Int || (col.tpe match { case OType.Con(s, _) => s.kind.isInstanceOf[TypeKind.Refinement]; case _ => false })
      )
      if !c.hasModes then
        rules.filter(r => headRel(r).contains(c)).iterator.map { r =>
          val Term.App(_, hs) = r.heads.head: @unchecked
          val atomsOfC = r.body.collect { case a @ Formula.Atom(RelRef.Sym(x), _, _) if inC(x) => a }
          atomsOfC.find(_.rel.sym != c).map(a => (s"the rule calls `${a.rel.sym.name}`, which is in the same component", a.span, Some(r)))
            .orElse(atomsOfC.iterator.map { call =>
              val s = call.args(k)
              val h = hs(k)
              if !decreases(s, h, r.body) then
                Some((s"no decrease: `${ObjPrinter.term(s)}` is not smaller than `${ObjPrinter.term(h)}`", call.span, Some(r)))
              else if !anchored(s, h, r.body, inC, numeric) then
                val msg =
                  if numeric then
                    s"no anchor: the body does not bound `${ObjPrinter.term(s)}` by a literal (e.g. `${ObjPrinter.term(s)} < 100`)"
                  else s"no anchor: the variables of `${ObjPrinter.term(h)}` are not bound by a relation outside the component"
                Some((msg, call.span, Some(r)))
              else None
            }.collectFirst { case Some(v) => v })
        }.collectFirst { case Some(v) => v }
      else
        val notInput = c.modes.find((m, _) => !m.inputs.lift(k).contains(true))
        notInput.map((m, sp) => (s"argument ${k + 1} is not an input of mode ${m.show}", sp, None)).orElse {
          rules.filter(r =>
            headRel(r).exists(isDemandOf) && r.body.exists {
              case Formula.Atom(RelRef.Sym(x), _, _) => inC(x)
              case _ => false
            }
          ).iterator.map { r =>
            val Term.App(RelRef.Sym(d), us) = r.heads.head: @unchecked
            val pos = inputIndex(d, c, k)
            r.body.headOption match
              case Some(g @ Formula.Atom(RelRef.Sym(gd), ws, _)) if isDemandOf(gd) =>
                val gpos = inputIndex(gd, c, k)
                (pos, gpos) match
                  case (Some(i), Some(j)) =>
                    val u = us(i)
                    val w = ws(j)
                    if !decreases(u, w, r.body) then
                      Some((
                        s"no decrease: demand `${ObjPrinter.term(u)}` is not smaller than `${ObjPrinter.term(w)}`",
                        r.heads.head.span,
                        Some(r)
                      ))
                    else if numeric && !r.body.exists {
                        case Formula.Cmp(CmpOp.Gt | CmpOp.Ge, x, Term.Lit(_)) => x == u
                        case Formula.Cmp(CmpOp.Lt | CmpOp.Le, Term.Lit(_), x) => x == u
                        case _ => false
                      }
                    then
                      Some((
                        s"no anchor: the body does not bound the demanded `${ObjPrinter.term(u)}` below by a literal (e.g. `${ObjPrinter.term(u)} >= 0`)",
                        r.heads.head.span,
                        Some(r)
                      ))
                    else None
                  case _ => Some(("the terminating argument is not an input of the demand", r.span, Some(r)))
              case _ => Some(("a demand rule without guard", r.span, Some(r)))
          }.collectFirst { case Some(v) => v }
        }
    }

  private def inputIndex(d: RelSym, c: RelSym, k: Int): Option[Int] = d.kind match
    case RelKind.Demand(_, m) if m.inputs.lift(k).contains(true) => Some(m.inputs.take(k).count(identity))
    case _ => None

  /** u ≺ w: structural (u a variable strictly inside the pattern w) or numeric (w = u + l). */
  private def decreases(u: Term, w: Term, body: List[Formula]): Boolean =
    def strictlyInside(v: String, t: Term): Boolean = t match
      case Term.App(_, as) => as.exists(a => Moding.vars(a).contains(v))
      case Term.As(x, _) => strictlyInside(v, x)
      case Term.Ascr(x, _) => strictlyInside(v, x)
      case _ => false
    def plus(big: Term, small: Term): Boolean = big match
      case Term.Arith(ArithOp.Add, x, Term.Lit(hugin.syntax.Literal.IntL(l))) => x == small && l > 0
      case Term.Arith(ArithOp.Add, Term.Lit(hugin.syntax.Literal.IntL(l)), x) => x == small && l > 0
      case _ => false
    def minus(small: Term, big: Term): Boolean = small match
      case Term.Arith(ArithOp.Sub, x, Term.Lit(hugin.syntax.Literal.IntL(l))) => x == big && l > 0
      case _ => false
    val structural = u match
      case Term.Var(v) => strictlyInside(v, w)
      case _ => false
    structural || plus(w, u) || minus(u, w) || body.exists {
      case Formula.Cmp(CmpOp.Eq, a, b) =>
        (a == w && plus(b, u)) || (b == w && plus(a, u)) || (a == u && minus(b, w)) || (b == u && minus(a, w))
      case _ => false
    }

  private def anchored(s: Term, h: Term, body: List[Formula], inC: Set[RelSym], numeric: Boolean): Boolean =
    val hv = Moding.vars(h)
    val boundOutside =
      body.collect { case Formula.Atom(RelRef.Sym(x), as, v) if !inC(x) => as.flatMap(Moding.vars).toSet ++ v }.flatten.toSet
    val structuralAnchor = hv.nonEmpty && hv.subsetOf(boundOutside)
    val numericAnchor = numeric && body.exists {
      case Formula.Cmp(CmpOp.Lt | CmpOp.Le, x, Term.Lit(_)) => x == s
      case Formula.Cmp(CmpOp.Gt | CmpOp.Ge, Term.Lit(_), x) => x == s
      case _ => false
    }
    structuralAnchor || numericAnchor
