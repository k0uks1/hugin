# Implementation notes

Decisions, deviations from the definition (draft revision 7), and observations about the draft made
while implementing it. Section numbers refer to the definition.

## Status against the milestones of Appendix A.3

| milestone | status |
|---|---|
| 1. Untyped core: parser, core IR, interning store, semi-naive evaluation, stratified negation, output | done |
| 2. Object types and records: declarations, inference, unions and open types, tag tests, named patterns, projection, update | done |
| 3. Arithmetic, aggregates, queries | done |
| 4. Modes and provenance: demand transformation, derivations | done |
| 5. Checks: completeness discipline, termination, `%partial` budgets, `%open` | done |
| 6. Meta level: stage inference, meta evaluator, modules and functors, formula functions, families, monomorphization | done |

All twelve conformance tests of Appendix A.2 are in `tests/` (see the README).

## Observations about the definition

### Nested head constructors and the evaluation order (Proposition 8.8)

The proof of Proposition 8.8 relies on: *"every relation occurring in a head of P_i, also nested,
belongs to P_i or to a component that depends on it"*. The dependency graph of Section 6.4 does not
guarantee this. Counterexample:

```
w : type.   mk : int -> w.
src : int -> rel.   src 1.
r : int -> rel.     r N :- mk N.
h : w -> rel.       h (mk N) :- src N.
```

The edges are `r → mk`, `mk → src` (from the nested constructor of `h`'s head) and `h → src`. A
topological order compatible with the stratification is `src, mk, r, h`. Evaluating by Definition 8.7
gives `M = {src 1, h (mk 1), mk 1}`, which is not a model: `mk 1 ∈ M` but `r 1 ∉ M`. The
implementation follows Definition 8.7 exactly (and Theorem 9.2 holds for it), so it reproduces this
result; `--lint` reports the situation as warning W0004.

Two obvious repairs have costs that showed up in the conformance tests:

* Adding an edge `c' → h` for every relation `c'` heading a new constructor term in a head of `h`
  restores the property, but it merges the fact relation of an update with the updating rule
  (`moved (E with {...}) :- unbound E` reads `var` through the inserted guard `(var Z̄ as E)` and
  constructs `var` facts), and likewise derivation rules (`@p2 (path X Z) I1 I2` constructs `path`).
  Those components then contain constructive rules and are rejected by the termination check, although
  they are finite.
* Adding edges `reader → h` (every relation reading `c'` depends on the rule constructing it) avoids
  the merge in the update and derivation cases (the reader is the rule itself) and repairs the
  counterexample, but makes evaluation order depend on readers and still needs an argument for readers
  inside `h`'s own component (where newly constructed facts are not part of any delta).

### Moded numeric termination (Definition 10.3)

The moded numeric case requires the body of a propagation rule to contain `u_k > b` or `u_k ≥ b`
syntactically. With `fib N F :- N > 1, A = N - 1, fib A FA, ...` the bound is on `N`, not on the
demanded `A`, so the natural formulation is rejected. The implementation derives such bounds (see
"Termination" below), and `tests/run/f_fib_moded.hgn` now uses the natural formulation.

### Demand components and termination (Definition 10.3)

Definition 10.3 checks the propagation rules `d(ū) :- d(w̄), …` *of the component of c*. The demand
relation of `c` need not be in that component: `c X Y :- c X Z, Y = Z + 1` with `%mode c + -` gives the
propagation rule `c^d X :- c^d X`, which forms a component of its own; that component has no constructive
rule, and `c`'s component has no propagation rule, so both pass, although `?- c 1 Y` derives `c 1 0`,
`c 1 1`, … forever (`tests/neg/t_termination_demand_loop.hgn`). Likewise a rule of `c` may call a relation
`d` of the component without a measure that reads `c`'s answers (`c X Y :- d X Z, Y = Z + 1` with
`d X Z :- dom X, c X Z`): no demand rule decreases, and the answers grow without new demands
(`tests/neg/t_termination_mutual_unmeasured.hgn`). Both programs were accepted before issue #2; the
check below closes both gaps.

### Ascriptions (Section 6.1)

`Γ ⊢ t : τ` in the ascription rule is read as the type of the *position* the ascribed term occupies
(the column type), because for a variable the meet of its expected types already includes the ascribed
type itself. Consequently `(P : person)` in a column of type `student | teacher` is rejected (an open
type is not a subtype of a union of fact types even if its members are), while `(P : student)` is
accepted.

### Brace disambiguation (Section 2.2)

"One token of lookahead past the first identifier" does not distinguish a record type from a module
body that starts with a declaration, e.g. `tc (g : graph) = { path : g.node -> g.node -> rel. ... }`
(Section 13.1). The parser therefore also scans for the first `,`, `.` or closing `}` at nesting depth 0:
a period first means a module body.

### Query answers

A query mentioning a projection or a disjunction elaborates into several alternatives; their answers
are united. Answers are restricted to the user's variables (no wildcards, no variables introduced by
elaboration, no variables local to negations or aggregates).

## Implementation decisions

* **Meta typing of object code.** The typer checks object code inside meta functions for staging,
  arity, labels and modes of signatures once, with parameters abstract. Object-level *typing* (meets,
  subsumption) runs on the elaborated, monomorphic program; errors in generated code carry the
  meta-level call chain (`note: in application of tc`). Accordingly `⇑τ ≤ ⇑τ'` is accepted at the meta
  level and checked after elaboration. Relation types are compared invariantly (after normalization).
* **Static normal forms.** Types mention meta values only through paths; dependent application
  substitutes the elaborated argument and normalizes symbolically (projection of record literals,
  transparent definitions). Module bodies are generative and never reduced in types.
* **Implicit type parameters** are solved by first-order matching of the argument meta types. An
  implicit parameter that is only constrained by object variables (which have no meta type) is accepted
  when it does not occur in the result type; it is then instantiated with an error type.
* **Families.** Instances are named `f[τ̄]` (e.g. `cons[int]`, rules `@l1[int]`); output uses the
  generic name (Section 9.6). Instantiating an open family also instantiates the constructors whose
  result is that family applied to their own parameters, so `mem(list[int])` is complete. Instantiation
  is capped at 10 000 instances.
* **Type definitions** are always unfolded; strict definitions are not folded back in diagnostics.
* **Formula functions.** Every literal object variable of a quote is renamed at each application
  (hygiene, Section 4.8); renamed variables print without the suffix. `%mode f m̄` is checked once on
  the body applied to fresh variables; uses are checked by the ordinary moding of the expanded rule.
* **`%infix`.** An operator declared with precedence `p` gets level `10p + 5` on the scale where the
  built-in levels of Section 2.2 are 10 (`;`) … 70 (`* /`); rule heads are parsed above the comparison
  level, so operators with `p ≥ 5` may appear in heads.
* **Layout heuristic.** An argument cannot start a line in column 0. This only matters for error
  recovery: a missing period at the end of an item is reported and the next item is still parsed.
* **Disjunction inside aggregates** (not covered by Section 7.2, which splits disjunctions of rule
  bodies only) is lifted into an auxiliary relation `aux(ī, ō)` with one rule per alternative. The
  inputs `ī` are the disjunction's variables bound before it in canonical order; the outputs `ō` are the
  variables bound by *every* alternative. A variable bound by only some alternatives is existential
  within its alternative: Definition 8.4 would otherwise range over unconstrained valuations. If there
  are inputs, `aux` is moded `+…+-…-`, so the demand transformation supplies the input bindings that
  arise at the call site. The aggregate then counts distinct bindings of its variables as usual.
  This is the semantics proposed for issue #1, item B4.

  *Demand of `aux` (issue #1, F1).* The aggregate is a negative edge `h → aux` of the rule's head `h`.
  Built from the whole prefix of the call (as Section 7.3 does for other calls), the demand rule
  `aux^d(ī) :- prefix` reads the atoms before the aggregate, which in a recursive rule include `h`'s own
  component: `s X :- p X _, s X, N = count { V | e V ; p X V }, N > 0` became the cycle
  `s → not s^or1 → s^or1^d → s` (E0601) although the source program is stratified. The demand rule of
  `aux` therefore keeps only the formulas of the prefix (in canonical order) that mention no relation
  depending on `h` — in the dependency graph without these demand rules — and are well-moded without
  the dropped ones, provided they still bind `ī`: `s^or1^d X :- p X _`.
  - *Answers.* The kept formulas are a subset of the conjunction that holds at the call, so every input
    binding that arises at the call is demanded, and `aux` is complete for it (Section 7.3, magic sets
    with a weaker guard). Extra demanded bindings only compute extra facts of `aux`, which only this
    aggregate reads, always with its own inputs bound, so the aggregate's value is unchanged.
  - *Stratification.* The kept formulas do not depend on `h`, so `aux^d` (and with it `aux`) no longer
    depends on `h`'s component through them: the negative edge `h → aux` leaves the component. The
    kept demand rule reads a subset of the relations the full one reads, so the change only removes
    edges: no cycle is introduced and no program accepted before is rejected.
  - *Fallback.* If the outer variables are bound only through relations that depend on `h`
    (`s Y :- s X, Y = X + 1, N = count { V | e V ; p Y V }`), the whole prefix is used and the cycle is
    reported (E0601, with a note naming the disjunction; `tests/neg/f_aggregate_disjunction_cycle.hgn`).
    Such a program is stratified in the source; accepting it would need disjunctions inside aggregates in
    the core (the aggregate would range over the alternatives directly) instead of the lifting.
* **Demand relations** are named `c^d[m]`, derivation relations `@r` or `@r#i`. Derivation relations
  are output relations; they cannot be referenced in atoms.
* **Primitives.** Integer overflow and division by zero (also for floats) are undefined. Strings
  compare by code point. NaN is never produced by the primitive operations.
* **Input facts** are accepted for relations declared `%input` or `%open`.
* **Dependency graph.** Exactly Section 6.4 (see the observation above).
* **Engine.** Identities are `(relation, n)` pairs; relations store tuples in insertion order, so
  old/delta/full windows are id ranges. Hash indexes are created for every set of bound columns that
  occurs in a `Scan`. Bodies are executed by backtracking over the IR; aggregates collect one value per
  distinct binding of the aggregate's local variables (Definition 8.4).

## Termination (issue #2)

The termination check (`obj/check/Termination.scala`) generalises Definition 10.3. A recursive
component (Section 6.4) needs a justification only if one of its rules is constructive (Definition 10.1);
a component with a `%partial` relation is evaluated with the round budget and not checked. Otherwise every
relation of the component, or the relation its demand relations belong to, may carry a measure
`%terminates X (c … X …)`, `%terminates l c`, or lexicographically `%terminates (X, Y) (c … X … Y …)` /
`%terminates (l, m) c`. `--explain-termination` prints, for every recursive component, which case
applies and the justification of every recursive step.

**Constructive rules (Definition 10.1, refined; issue #1, F3).** Clause (a) of Definition 10.1 counts
every constructor term of a head that is not matched in the body (issue #1, B9: the arguments themselves
included). The implementation counts such a term only if it can take infinitely many values over the
evaluation of the component: it is *not* constructive when it is ground (`d X red :- d X _`, `e (mk 1)`)
or when each of its variables occurs in a positive body atom of a *plain* relation outside the component
(`e X (mk Y) :- e X _, b Y`). Clauses (b) (a matched fact lifted into the head) and (c) (arithmetic in the
head or computing a head variable) are unchanged.

*Soundness.* The argument for components without constructive rules was: their facts consist of terms
that exist before the component is evaluated, a finite set, so the fixed point is finite. With the
refinement, the terms a rule can construct are the instances of its non-constructive head terms. A
ground term has one instance. A term whose variables occur in positive atoms of plain relations outside
the component has one instance per valuation of those variables, and each such variable is a subterm of a
fact of such a relation (or the fact itself, for `as` variables). Those relations belong to earlier
components, which are complete when this component is evaluated (Definition 8.7) and finite by induction
over the evaluation order (recursive components are checked here or `%partial` with a budget; others are
finite in their inputs). Plain relations only get facts from their own rules, so they do not grow later.
So every rule constructs terms from a fixed finite set, and the component's facts consist of the existing
terms plus that set: still finite. Constructor and struct relations do not count as finite sources even
outside the component, because a nested head constructor can create their facts after their component
(issue #1, A1), including the rule itself: `d (s (s N)) :- s N` makes `s (s N)` and then matches it
(`tests/neg/t_termination_ctor_source.hgn`); the anchor condition below still counts every relation
outside the component as finite, constructor relations included, which deserves the same caution. Variables bound only by equations, arithmetic or aggregates
keep the term constructive (conservative). In the measured cases the conditions "rules of unmeasured
relations are not constructive" use the same notion; there "only copy existing terms" becomes "construct
terms from a fixed finite set", which the arguments below need in the same way (finitely many facts per
round, finitely many terms overall). `tests/run/t_termination_finite_ctors.hgn` shows the accepted cases.

**Measures.** A measure is a tuple of argument positions; all measured relations of a component have
tuples of the same length, and slot `i` is of the same kind for all of them: *integer* slots (`int` or a
refinement of `int`) are ordered by `<`, *structural* slots (any other type) by the proper-subterm
relation. Tuples are compared lexicographically; a step *decreases at slot i* if slots `< i` are equal
and slot `i` decreases. Both orders are strict partial orders, so the lexicographic order is one too.

**Arithmetic facts.** For a rule body, `Arithmetic` (`obj/check/Intervals.scala`) computes an interval for
every integer term from the comparisons `l op r` (`op` in `= < ≤ > ≥`) by propagation to a bounded fixed
point, through `+`, `-`, unary minus, multiplication by a literal and truncating division by a positive
literal (both directions: `A = N - 1` with `N > 1` gives `A ≥ 1`, and `A ≥ 1` gives `N ≥ 2`). A
difference `a - b` is bounded by rewriting the linear form of `a - b` with the linear equations of the
body (adding multiples of `l - r = 0`) up to a small depth and intersecting the intervals of all forms.
Every step preserves the invariant *if a valuation satisfies the body, every term's value lies in its
interval and every form has the value of `a - b`*: comparisons hold by assumption, interval arithmetic
over-approximates the operations (overflow and division by zero are undefined, so such a valuation does
not satisfy the body), and the forms differ by multiples of zero. `IntervalsSuite` checks this invariant
on random satisfied bodies. Equal: `a = b` syntactically, or `a - b ∈ [0, 0]`, or (structural) an
equation `a = b` in the body. Integer decrease: `b - a ≥ 1`, or `a = x / l` with `l ≥ 2`, `x ≤ b` and
`x ≥ 1` (`0 ≤ x / l < x` then). Structural decrease: `a` is a proper subterm of `b`, unfolding variables
of `b` bound to patterns by `P as V`, `(c t̄ as V)` or `V = c t̄`. Only integer slots consult intervals;
since comparisons and equations relate terms of one type, float and string comparisons never bound an
integer term.

**Bottom-up components** (no measured relation has modes). Conditions:

1. Rules of unmeasured relations in the component are not constructive.
2. In a rule with head `c h̄`, `c` measured, every body atom `d s̄` of the component is of a measured
   relation, and the measure decreases from the call to the head: `μ_d(s̄)` is lexicographically below
   `μ_c(h̄)`, decreasing at slot `i`.
3. Anchor: for slot `i` the head's value lies below a bound (`h_i ≤ B`), and for every later slot `j > i`
   it lies in a finite set (`L ≤ h_j ≤ B`). A slot is bounded if its variables are bound by positive
   atoms of relations outside the component (a finite set: those relations are finite by induction over
   the evaluation order), or by its interval, or by the call's slot (bounded likewise) plus a bounded
   difference `h_j - s_j`. Structural slots must be bound by relations outside the component.

*Soundness.* In semi-naive evaluation a fact that is new in round `r > 1` is derived by a rule with a
premise of the component that is new in round `r - 1`; so a fact of round `r` ends a chain
`m_1 < m_2 < … < m_r` (by condition 2, through measured relations only) that starts at a fact of a rule
without premises of the component, of which there are finitely many. Along the chain slot 1 never
decreases; it increases only at steps whose head value is `≤ B`, so all values of slot 1 lie between the
minimum over the start facts and the maximum of `B` and the start facts. For slot `j > 1`, a segment of
the chain in which slots `< j` are constant starts at a start fact or at a step decreasing at an earlier
slot, whose slot `j` lies in a finite set by condition 3, and then increases only to values `≤ B`.
Hence all measures on chains come from one finite set and chains are no longer than its size; the
component reaches its fixed point after boundedly many rounds, each of which derives finitely many facts.
Unmeasured relations (condition 1) only copy existing terms or construct terms from a fixed finite set.
The previous check (one slot, syntactic
`s < b`, `w = u + l`, structural anchor on the head) is the special case with `n = 1`.

**Demand-driven components** (a measured relation has modes; all measured relations must have modes,
and every measured position is an input of every mode). Conditions:

1. Rules whose head is neither measured nor a demand relation of a measured relation are not
   constructive.
2. A rule of a measured relation calls relations of the component only if they are measured, demand
   relations, or unmeasured relations that do not depend on answers of measured relations other than
   through demand relations (the type checker's `lookup` depends only on `bind` facts constructed by
   demands).
3. Every propagation rule `e^d(ū) :- g^d(w̄), …` whose guard is a demand of a measured relation `g` (in
   any component — the demands of `log2` form their own component), and every propagation rule of the
   component that reads the component, decreases the measure from guard to head: `μ_e(ū) < μ_g(w̄)`,
   decreasing at slot `i`; if slot `i` is an integer, the body bounds `u_i` below (or binds it by relations
   outside the component). Later slots are unconstrained (Ackermann: `ack (M - 1) R1 R` with `R1`
   computed).

*Soundness.* By condition 3 every chain of demand facts, each derived from the previous one as guard, is
lexicographically decreasing, and the order is well founded on the values that occur: slot 1 never
increases and decreases only to values above a fixed bound, so it decreases finitely often; then slot 2,
and so on (structural slots decrease in the well-founded subterm order). Demands are seeded by finitely
many facts (propagation rules without premises of the component and queries). By well-founded induction
on the demand, the facts demanded under a demand `p` are finite: the answers of `p` are derived by rules
guarded by `p` whose atoms of the component are measured (and guarded by demands that are children of
`p`, finitely many by induction since they are derived from `p`, finitely many answers of earlier
children and finite relations), demand relations, or relations that depend only on demands (condition 2);
the terms they construct come from finitely many valuations. König's lemma (finitely many seeds, finite
branching, no infinite chain) bounds the set of demands, and so the component. Unmeasured relations only
copy existing terms or construct terms from a fixed finite set (condition 1).

**Diagnostics.** E0603 names the constructive rule, the cycle through the component, and a measure that
would be accepted (single positions per relation, or a lexicographic pair for a single relation, found by
running the check) or `%partial`. E0604 points at the call (or the demanded call) that fails, labels the
head's or caller's measure, says which slot of the measure fails and whether the decrease or the anchor
is missing, and suggests the missing comparison or `%partial`. Components with a cycle through negation
are skipped (E0601 is reported).

**Not covered.** Measures through non-linear arithmetic other than division by a literal, multiset or
size-change termination with permuted arguments (Lee, Jones, Ben-Amram), declared measure functions,
anchors through finite (non-recursive) types, and bottom-up structural recursion whose head is not
matched against existing facts.

## Possible next steps

* Object-level typing of functor bodies with abstract types (earlier errors for functors).
* Size-change termination (Lee, Jones, Ben-Amram) for argument permutations in the termination check.
* A faster engine (columnar storage, join planning) behind the same core IR.
