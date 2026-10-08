package hugin.obj
package check

import hugin.util.*

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
  def constructive(r: Rule, inC: RelSym => Boolean): Option[(String, Span)] =
    val finite = finiteVars(r.body, inC)
    val headVars = r.heads.flatMap(keyArgs).flatMap(Moding.vars).toSet
    val atomVars = r.body.collect { case Formula.Atom(_, as, v) => as.flatMap(Moding.vars).toSet ++ v }.flatten.toSet
    val existing = DepGraph.positiveSubpatterns(r.body)
    def builds(t: Term): Boolean = t match
      case a @ Term.App(RelRef.Sym(c), as) => (c.isData && !existing(a)) || as.exists(builds)
      case Term.As(x, _) => builds(x)
      case Term.Ascr(x, _) => builds(x)
      case _ => false
    DepGraph.newHeadConstructors(r, withHead = true).find(t => !Moding.vars(t).subsetOf(finite)).map(t =>
      (s"its head constructs `${ObjPrinter.term(t)}`, which is not matched in the body", t.span)
    )
      .orElse {
        // `X = c t̄` with a data term binds `X` to a new value unless `X` is bound by an atom (a test)
        r.body.collectFirst(Function.unlift {
          case c @ Formula.Cmp(CmpOp.Eq, l, rr) =>
            List((l, rr), (rr, l)).collectFirst {
              case (Term.Var(x), e) if headVars(x) && !atomVars(x) && builds(e) && !Moding.vars(e).subsetOf(finite) =>
                (s"head variable `${Var.display(x)}` is built by `${ObjPrinter.formula(c)}`", c.span)
            }
          case _ => None
        })
      }
      .orElse {
        val asVars = r.body.collect { case Formula.Atom(_, _, Some(v)) => v }.toSet
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
        r.heads.flatMap(keyArgs).flatMap(arith).headOption.map(t => (s"its head computes `${ObjPrinter.term(t)}`", t.span))
      }
      .orElse {
        r.body.collectFirst {
          case c @ Formula.Cmp(CmpOp.Eq, Term.Var(x), e) if headVars(x) && hasOp(e) =>
            (s"head variable `${Var.display(x)}` is computed by `${ObjPrinter.formula(c)}`", c.span)
          case c @ Formula.Cmp(CmpOp.Eq, e, Term.Var(x)) if headVars(x) && hasOp(e) =>
            (s"head variable `${Var.display(x)}` is computed by `${ObjPrinter.formula(c)}`", c.span)
        }
      }

  /** The arguments of a head that can invent values: all but a bound column. The values of a bound column
   *  are kept finite per key by evaluation (the best value, or `∞` when it would improve forever,
   *  docs/REDESIGN.md §5.2), so a component whose invention is only through bound columns terminates
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
   *  is split into `s (s N) :- s N`, which is checked in `s`'s component). A data constructor has no
   *  facts; an atom over it is a generated guard `(c Z̄ as X)` destructuring the value of `X`, so its
   *  variables are finite if `X` is. */
  def finiteVars(body: List[Formula], inC: RelSym => Boolean): Set[String] =
    var vars = body.collect {
      case Formula.Atom(RelRef.Sym(x), as, v) if !inC(x) && !x.isData => as.flatMap(Moding.vars).toSet ++ v
    }.flatten.toSet
    val guards = body.collect { case Formula.Atom(RelRef.Sym(x), as, Some(v)) if x.isData => (v, as.flatMap(Moding.vars).toSet) }
    var changed = true
    while changed do
      changed = false
      for (v, inner) <- guards if vars(v) && !inner.subsetOf(vars) do
        vars ++= inner
        changed = true
    vars
