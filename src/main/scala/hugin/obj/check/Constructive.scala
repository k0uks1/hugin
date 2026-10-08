package hugin.obj
package check

import hugin.obj.typing.Moding

/** Constructive rules (Definition 10.1, refined) and finite sources: what makes a recursive component
 *  need a termination argument (docs/NOTES.md, "Termination"). */
object Constructive:
  /** Why a rule of the component `inC` is constructive (Definition 10.1, refined), if it is.
   *
   *  A rule is constructive if it builds a constructor term, data or fact, that is not matched in the body,
   *  in a head (also through a head variable bound by a binding equation `X = c t̄` with a data term, which
   *  builds the value) or in a moded input (the head of a demand rule). Such a term counts only if it can
   *  take infinitely many values: a ground term (`red`, `mk 1`) is one fixed term, and a term whose
   *  variables are all [[Constructive.finiteVars]] ranges over finitely many valuations, since the relations
   *  binding them are complete and finite when the component is evaluated (induction over the evaluation
   *  order). See docs/NOTES.md, "Termination" (issue #1, F3).
   */
  def constructive(r: Rule, inC: RelSym => Boolean): Option[Invention] =
    val finite = finiteVars(r.body, inC)
    val headVars = r.heads.flatMap(keyArgs).flatMap(Moding.vars).toSet
    DepGraph.newHeadConstructors(r, withHead = true).find(t => !Moding.vars(t).subsetOf(finite)).map(Invention.HeadConstructs(_))
      .orElse {
        val asVars = r.body.collect { case Formula.Atom(_, _, Some(v)) => v }.toSet
        asVars.intersect(headVars).headOption.map(v => Invention.LiftedFact(VarName(v), r.span))
      }
      .orElse {
        def arith(t: Term): Option[Term] = t match
          case a: Term.Arith => Some(a)
          case n: Term.Neg => Some(n)
          case Term.App(_, as) => as.flatMap(arith).headOption
          case Term.As(x, _) => arith(x)
          case Term.Ascr(x, _) => arith(x)
          case _ => None
        r.heads.flatMap(keyArgs).flatMap(arith).headOption.map(Invention.HeadComputes(_))
      }
      .orElse {
        r.body.collectFirst {
          case c @ Formula.Cmp(CmpOp.Eq, Term.Var(x), e) if headVars(x) && hasOp(e) => Invention.ComputedByEquation(VarName(x), c)
          case c @ Formula.Cmp(CmpOp.Eq, e, Term.Var(x)) if headVars(x) && hasOp(e) => Invention.ComputedByEquation(VarName(x), c)
        }
      }

  /** The arguments of a head that can invent values: all but a bound column. The values of a bound column
   *  are kept finite per key by evaluation (the best value, or `∞` when it would improve forever,
   *  reference: object/bound-columns), so a component whose invention is only through bound columns terminates
   *  when its keys do. */
  def keyArgs(head: Term): List[Term] = head match
    case Term.App(RelRef.Sym(h), as) if h.boundColumn.isDefined => as.init
    case Term.App(_, as) => as
    case _ => Nil

  private def hasOp(t: Term): Boolean = t match
    case _: Term.Arith | _: Term.Neg => true
    case Term.App(_, as) => as.exists(hasOp)
    case _ => false

  /** Variables of `body` bound by positive atoms of relations outside the component `inC` that are finite
   *  sources: complete and finite when the component is evaluated (induction over the evaluation order).
   *  Fact constructors and fact structs are finite sources too: a nested head term `c t̄` asserted by a
   *  rule of a later component is also derived by its split rule in `c`'s component (Proposition 8.8,
   *  `StratifyPhase.splitRules`), so no fact is added to `c` after its component (`d (s (s N)) :- s N`
   *  is split into `s (s N) :- s N`, which is checked in `s`'s component). */
  def finiteVars(body: List[Formula], inC: RelSym => Boolean): Set[String] =
    body.collect { case Formula.Atom(RelRef.Sym(x), as, v) if !inC(x) => as.flatMap(Moding.vars).toSet ++ v }.flatten.toSet
