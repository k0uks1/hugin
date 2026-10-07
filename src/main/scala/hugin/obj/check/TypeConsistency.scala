package hugin.obj
package check

import hugin.util.*
import hugin.syntax.Bound
import hugin.obj.typing.Moding

/** Type-consistency of a rule over bound columns (Kaminski et al., IJCAI 2017; Berent et al., Def. 4;
 *  docs/REDESIGN.md §5.2), E0606.
 *
 *  The *limit variables* of a rule are the variables in the bound column of its positive body atoms over
 *  bound relations of the head's component (`inC`); relations of earlier components are complete, so
 *  their values are constants. A limit variable occurs in exactly one atom and elsewhere only linearly
 *  (non-zero integer coefficients, after replacing variables defined by binding equations), in the bound
 *  column of a bound head and in order comparisons, each in the direction in which improving the atom's
 *  value improves the head or keeps the comparison true:
 *
 *  - a `min` head: positive coefficients from `min` atoms, negative ones from `max` atoms (dually `max`);
 *  - `s₁ < s₂` (`≤`, and `>`/`≥` swapped): in `s₁ - s₂` positive coefficients from `min` atoms, negative
 *    ones from `max` atoms.
 *
 *  Then the program is *stable*: a rule that applies keeps applying to better values and its head improves
 *  at least as much, so reading the best value per key computes the least limit-closed model and a
 *  positive cycle of value propagation diverges (see `runtime/Divergence.scala`). */
object TypeConsistency:
  /** A limit variable: the atom binding it and the kind of that atom's bound column. */
  private final case class Limit(atom: Formula.Atom, kind: Bound)

  def check(r: Rule, inC: RelSym => Boolean): Option[Diagnostic] =
    val limits = limitVars(r, inC)
    malformedAtom(r, inC).orElse(Option.when(limits.nonEmpty)(Checker(r, limits).firstViolation).flatten)

  /** The atoms of `r` over bound relations of its component whose value flows into the head's bound
   *  column (the edges of the value propagation graph, `runtime/Divergence.scala`). */
  def propagating(r: Rule, inC: RelSym => Boolean): List[Formula.Atom] =
    val limits = limitVars(r, inC)
    val headTerm = r.heads.headOption.collect { case Term.App(RelRef.Sym(h), args) if h.boundColumn.isDefined => args.last }
    headTerm.toList.flatMap { t =>
      val vars = Moding.vars(Checker(r, limits).expanded(t))
      limits.collect { case (v, l) if vars(v) => l.atom }.toList.distinct
    }

  /** The limit variables of `r`, by name. */
  private def limitVars(r: Rule, inC: RelSym => Boolean): Map[String, Limit] =
    r.body.collect {
      case a @ Formula.Atom(RelRef.Sym(b), args, _) if inC(b) && b.boundColumn.isDefined =>
        args.lastOption.collect { case Term.Var(v) => v -> Limit(a, b.boundColumn.get) }
    }.flatten.toMap

  /** The bound column of an atom of the component must be a variable (or `_`): a constant would test the
   *  best value for equality, which is not monotone. */
  private def malformedAtom(r: Rule, inC: RelSym => Boolean): Option[Diagnostic] =
    r.body.collectFirst(Function.unlift {
      case Formula.Atom(RelRef.Sym(b), args, _) if inC(b) && b.boundColumn.isDefined =>
        args.lastOption.filter {
          case _: Term.Var => false
          case _ => true
        }.map(t =>
          violation(
            t.span,
            s"the `${b.boundColumn.get.show}` column of `${b.name}` is not a variable",
            "a recursive atom over a bound column must bind its value to a variable",
            s"bind a variable and compare it, e.g. `${b.name} … D, D <= ${ObjPrinter.term(t)}`"
          )
        )
      case _ => None
    })

  private def violation(span: Span, msg: String, label: String, help: String, notes: List[String] = Nil): Diagnostic =
    val d = Diagnostic.error("E0606", s"type-inconsistent rule: $msg", span, label)
      .withNote(
        "in the recursion of a bound relation, improving a value read from a bound column must improve the head (or keep the body true), so that keeping only the best value per key is exact (docs/REDESIGN.md §5.2)"
      )
    (notes.foldLeft(d)(_.withNote(_))).withHelp(help)

  /** The checks of one rule with limit variables `limits`. */
  private final class Checker(r: Rule, limits: Map[String, Limit]):
    /** Variables defined by binding equations `X = t` over limit variables, as their (expanded) definitions. */
    private val definitions: Map[String, Term] =
      val atomVars = r.body.collect { case Formula.Atom(_, as, v) => as.flatMap(Moding.vars).toSet ++ v }.flatten.toSet
      var defs = Map.empty[String, Term]
      var changed = true
      while changed do
        changed = false
        for case Formula.Cmp(CmpOp.Eq, l, rr) <- r.body; case (Term.Var(x), t) <- List((l, rr), (rr, l)) do
          if !atomVars(x) && !limits.contains(x) && !defs.contains(x) && tainted(t, defs) then
            defs += x -> t
            changed = true
      defs.view.mapValues(expand(_, defs)).toMap

    private def tainted(t: Term, defs: Map[String, Term]): Boolean =
      Moding.vars(t).exists(v => limits.contains(v) || defs.contains(v))

    private def isTainted(t: Term): Boolean = tainted(t, definitions)

    private def expand(t: Term, defs: Map[String, Term]): Term = t match
      case Term.Var(v) if defs.contains(v) => expand(defs(v), defs)
      case Term.Arith(op, a, b) => Term.Arith(op, expand(a, defs), expand(b, defs))(t.span)
      case Term.Neg(a) => Term.Neg(expand(a, defs))(t.span)
      case Term.Ascr(a, tp) => Term.Ascr(expand(a, defs), tp)(t.span)
      case _ => t

    /** `t` with the variables defined by binding equations replaced by their definitions. */
    def expanded(t: Term): Term = expand(t, definitions)

    private def isDefinition(f: Formula): Boolean = f match
      case Formula.Cmp(CmpOp.Eq, Term.Var(x), _) if definitions.contains(x) => true
      case Formula.Cmp(CmpOp.Eq, _, Term.Var(x)) if definitions.contains(x) => true
      case _ => false

    /** The first occurrence of a tainted variable in `t`, for the diagnostic's span. */
    private def occurrence(t: Term): Term = t match
      case v @ Term.Var(x) if limits.contains(x) || definitions.contains(x) => v
      case _ => TreeLike.children(t).find(isTainted).map(occurrence).getOrElse(t)

    private def limitOf(t: Term): Option[Limit] = Moding.vars(expand(t, definitions)).flatMap(limits.get).headOption

    private def boundBy(l: Limit): (Span, String) =
      (l.atom.span, s"bound by this `${l.kind.show}` atom")

    private def misplaced(t: Term, where: String, help: String): Diagnostic =
      val o = occurrence(t)
      val d = violation(o.span, s"`${ObjPrinter.term(o)}` from a bound column is used $where", s"used $where", help)
      limitOf(o).map(boundBy).fold(d)((s, l) => d.withLabel(s, l))

    def firstViolation: Option[Diagnostic] =
      atomUses.orElse(tests).orElse(comparisons).orElse(head)

    /** Limit variables in other atom columns, a second bound atom, negations, aggregates or disjunctions. */
    private def atomUses: Option[Diagnostic] =
      r.body.iterator.flatMap {
        case a @ Formula.Atom(_, args, _) =>
          val own = limits.collect { case (v, l) if l.atom eq a => v }.toSet
          args.zipWithIndex.collectFirst {
            case (t, i) if isTainted(t) && !(i == args.length - 1 && Moding.vars(t).subsetOf(own) && t.isInstanceOf[Term.Var]) =>
              misplaced(
                t,
                "in a column of an atom",
                "compare it with `<`, `<=`, `>`, `>=` instead, or read the relation from a later component"
              )
          }
        case n: Formula.Not if formulaTainted(n) =>
          Some(violation(
            n.span,
            "a value from a bound column is negated",
            "uses a recursive bound value",
            "read the value outside the recursion"
          ))
        case g: Formula.Agg if formulaTainted(g) =>
          Some(violation(
            g.span,
            "a value from a bound column is aggregated",
            "uses a recursive bound value",
            "read the value outside the recursion"
          ))
        case d: Formula.Disj if formulaTainted(d) =>
          Some(violation(
            d.span,
            "a value from a bound column is used in a disjunction",
            "uses a recursive bound value",
            "split the rule into one rule per alternative"
          ))
        case _ => None
      }.nextOption()

    private def formulaTainted(f: Formula): Boolean = f match
      case Formula.Atom(_, args, _) => args.exists(isTainted)
      case Formula.Cmp(_, l, rr) => isTainted(l) || isTainted(rr)
      case Formula.Not(a) => formulaTainted(a)
      case Formula.Agg(_, _, t, b) => isTainted(t) || b.exists(formulaTainted)
      case Formula.Disj(alts) => alts.flatten.exists(formulaTainted)
      case _ => false

    /** `=` and `<>` tests (other than the binding equations of [[definitions]]) are not monotone. */
    private def tests: Option[Diagnostic] =
      r.body.collectFirst {
        case c @ Formula.Cmp(op @ (CmpOp.Eq | CmpOp.Ne), l, rr) if !isDefinition(c) && (isTainted(l) || isTainted(rr)) =>
          misplaced(
            if isTainted(l) then l else rr,
            s"in the test `${op.show}`",
            "compare with `<`, `<=`, `>` or `>=` (a bound value only improves)"
          )
      }

    /** `s₁ < s₂`: in `s₁ - s₂` positive coefficients come from `min` atoms, negative ones from `max` atoms. */
    private def comparisons: Option[Diagnostic] =
      r.body.iterator.collect {
        case c @ Formula.Cmp(op @ (CmpOp.Lt | CmpOp.Le | CmpOp.Gt | CmpOp.Ge), l, rr) if isTainted(l) || isTainted(rr) =>
          val (lo, hi) = if op == CmpOp.Lt || op == CmpOp.Le then (l, rr) else (rr, l)
          val diff = Term.Arith(ArithOp.Sub, expand(lo, definitions), expand(hi, definitions))(c.span)
          directions(diff, c.span, positive = Bound.Min, s"the comparison `${ObjPrinter.formula(c)}`")
      }.flatten.nextOption()

    /** The head: limit variables only in the bound column of a bound head, in the improving direction. */
    private def head: Option[Diagnostic] =
      r.heads.headOption.collect { case Term.App(RelRef.Sym(h), args) => (h, args) }.flatMap { (h, args) =>
        val kind = h.boundColumn
        val keys = if kind.isDefined then args.init else args
        keys.find(isTainted).map(t =>
          misplaced(
            t,
            if kind.isDefined then "in a key column of the head" else s"in the head of `${h.name}`, which has no bound column",
            "a recursive bound value can only flow into the bound column of a bound relation; read it from a later component to use it as a plain value"
          )
        ).orElse(kind.flatMap(k =>
          directions(expand(args.last, definitions), args.last.span, positive = k, s"the head's `${k.show}` column")
        ))
      }

    /** Checks the linear form of `t`: every limit variable has a non-zero coefficient, a positive one from
     *  an atom of kind `positive` and a negative one from the other kind. */
    private def directions(t: Term, span: Span, positive: Bound, where: String): Option[Diagnostic] =
      val lin = Linear.of(t)
      val nonLinear = lin.coeffs.keys.collectFirst {
        case a if !a.isInstanceOf[Term.Var] && Moding.vars(a).exists(limits.contains) => a
      }
      nonLinear match
        case Some(a) =>
          Some(
            violation(
              a.span,
              s"`${ObjPrinter.term(a)}` is not linear in a bound value",
              "not linear",
              "use only `+`, `-` and multiplication by an integer literal on bound values"
            )
          )
        case None =>
          val occurring = Moding.vars(t).filter(limits.contains)
          occurring.toList.sorted.iterator.flatMap { v =>
            val c = lin.coeff(Term.Var(v)(Span.NoSpan))
            val l = limits(v)
            val wanted = if c > 0 then positive else other(positive)
            if c == 0 then
              Some(violation(
                span,
                s"`${Var.display(v)}` cancels out in $where",
                "coefficient 0",
                "remove the variable or give it a non-zero coefficient"
              ))
            else if l.kind != wanted then
              val (s, lbl) = boundBy(l)
              Some(
                violation(
                  span,
                  s"`${Var.display(v)}` from a `${l.kind.show}` column has the wrong sign in $where",
                  s"improving `${Var.display(v)}` makes this worse",
                  s"in $where a value from a `${l.kind.show}` column needs a ${if l.kind == positive then "positive" else "negative"} coefficient"
                ).withLabel(s, lbl)
              )
            else None
          }.nextOption()

    private def other(b: Bound): Bound = if b == Bound.Min then Bound.Max else Bound.Min

/** Immediate subterms of a term. */
private object TreeLike:
  def children(t: Term): List[Term] = t match
    case Term.App(_, as) => as
    case Term.As(x, _) => List(x)
    case Term.Ascr(x, _) => List(x)
    case Term.Proj(v, _) => List(v)
    case Term.With(v, fs) => v :: fs.map(_._2)
    case Term.Arith(_, a, b) => List(a, b)
    case Term.Neg(a) => List(a)
    case _ => Nil
