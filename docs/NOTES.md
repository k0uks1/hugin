# Implementation notes

Decisions, deviations from the language definition draft (revision 7), and the arguments behind the checks
of the reference implementation, as they stand after the redesign (issue #40). Section numbers without a
prefix refer to the definition draft; `REDESIGN` refers to [`docs/REDESIGN.md`](REDESIGN.md).

These notes are a record, not the specification: the [language reference](https://k0uks1.github.io/hugin/) defines the language,
and where the two differ the reference applies. Notes that describe semantics the redesign replaced (the
pre-redesign meta level, the data/fact split, relation modes and the built-in demand transformation,
demand per call site, `%partial`) are in [`history/NOTES-pre-redesign.md`](history/NOTES-pre-redesign.md).

## Status

The milestones of Appendix A.3 of the definition draft are done, and the redesign phases A (size-change
termination, bound columns, removal of `%partial`), B (the dependent meta level), C1 (reflection), C2
(directives as meta functions) and C3 (`%demand` in the prelude) are done; Phase D (consolidation) is in
progress. The conformance tests of Appendix A.2 are `tests/run/a01`–`a12` and `tests/neg/a05`–`a11`,
rewritten for the new semantics where it changed (see CONTRIBUTING.md, "Tests").

## Observations about the definition

### Nested head constructors and the evaluation order (Proposition 8.8)

*Written when only `%fact` constructors asserted; since C3 every constructor is a fact constructor, and the
split rules below apply to all of them.*

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
gives `M = {src 1, h (mk 1), mk 1}`, which is not a model: `mk 1 ∈ M` but `r 1 ∉ M`. Since data
constructors never assert (see "Data and fact constructors" in the history), the gap only concerns fact constructors
(`%fact`) built in heads: with `mk` a data constructor the example has no fact `mk 1` and `r` is not
affected.

**Resolved by split rules** (`StratifyPhase.splitRules`). The rule: *if a rule `h … :- B` asserts a
fact-constructor term `c t̄` besides its own fact (a new F-term of its head outside the guarded input
columns, `DepGraph.assertedHeadConstructors`) and `c`'s component comes before `h`'s, the rule
`c t̄ :- B` is added and evaluated in `c`'s component.* (This is how Slog treats nested facts: every
nested fact gets a rule of its own.) The dependency graph already lets `c` depend on everything `B`
reads (Section 6.4, see "Dependency graph" below), so the split rule has exactly the edges
of the graph: the components and the stratification are unchanged, and stratification is checked on
the edges the split rules need. When `c`'s component is complete, so are `B`'s relations (they are
dependencies of `c`), hence the split rule derives every `c t̄` the original rule asserts later, and the
later assertions add nothing. So every component is complete after its evaluation, which is the
property the proof of Proposition 8.8 needs, and evaluation yields the least model
(`tests/run/n_nested_head_order.hgn` now answers `r 1`). Consequences:

* A rule that asserts `c` facts and negates or aggregates over a relation depending on `c` is a cycle
  through negation (E0601, with a note naming the asserting rule; `tests/neg/n_nested_head_negation.hgn`).
  Such a program has no stratified meaning: `r 1` would hold iff `mk 1` is asserted, which happens iff
  `r 1` does not hold. This was E0601 before too (the edges `c → B` exist since data constructors
  stopped asserting). Aggregates over `c` in other rules see all of `c`'s facts
  (`tests/run/n_nested_head_aggregate.hgn`).
* The split rule belongs to `c`'s component for the termination check: `d (s (s N)) :- s N` gives
  `s (s N) :- s N`, which creates `s` facts that it reads again (`tests/neg/t_termination_ctor_source.hgn`).
  A rule of a fact constructor builds its head fact even if its arguments are matched (Definition 10.1:
  the head itself is a constructor term); before, `s (s N) :- s N` written in the source was accepted
  and did not terminate (`tests/neg/t_termination_fact_head.hgn`).
* Fact constructors of earlier components are finite sources for the termination check (no fact is
  added to them after their component), see "Termination".
* Derivation rules are not split (the terms of their heads are facts derived by the rule they describe),
  nor are terms in guarded input columns (they match the demand and are facts already, E0504).
* W0004 (and `--lint`, which only enabled it) is removed: a fact term built in a head can no longer be
  missed by the readers of its constructor. Data terms never assert, so nothing remains for it to report.

On the whole corpus (goldens, examples, fuzz suites) no program becomes newly rejected: the split rules
add no edge, so there is no new E0601, and the only termination change is the component (`{s}` instead
of `{d}`) in which `t_termination_ctor_source` is rejected.

The alternatives are worse. Adding an edge `c → h` for every relation `c` heading a new constructor
term in a head of `h` also restores the property, but makes `c` depend on *all* rules of `h`, not just
the asserting one: in `tests/run/n_nested_head_strata.hgn` another rule of `h` reads `q`, which negates
a reader of `mk`, and the edge would make that a cycle through negation; likewise the fact relation of an
update or derivation would merge with the updating rule's component, which the termination check then
rejects. Adding edges `reader → h` makes the order depend on readers and needs an argument for readers
inside `h`'s own component.

### Ascriptions (Section 6.1)

`Γ ⊢ t : τ` in the ascription rule is read as the type of the *position* the ascribed term occupies
(the column type), because for a variable the meet of its expected types already includes the ascribed
type itself. Consequently `(P : person)` in a column of type `student | teacher` is rejected (an open
type is not a subtype of a union of fact types even if its members are), while `(P : student)` is
accepted.

The circularity only concerns variables. A term that is not a variable has its synthesized type and, by
subsumption, every supertype of it, so `Γ ⊢ t : τ` holds with `τ` the ascribed type itself whenever the
term's type is a subtype of it: `(nil : list int)` ascribes a constructor term with its declared result
type, which is accepted (also outside a column, e.g. in a comparison) and always holds, so no test is
needed (issue #1, F4). The term must still fit the column it occupies.

Type arguments of families are inferred by first-order matching (Section 4.6). In a comparison both
sides have one type; a constructor fact of a family stands for the constructor's declared result type
there, as it does when it solves a type parameter, so `L <> nil` with `L : list int` gives `nil[int]`, and
`cons 1 nil = nil` relates both type arguments. When nothing determines them, E0206 suggests the
ascription above with the missing parameters left for the user to fill in.

Comparisons with constructor terms are structural, nested terms included (`L = cons 1 nil`); see the reference,
[object/facts](https://k0uks1.github.io/hugin/object/facts.html).

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

* **Suggestions** (`util/Diagnostics`) are edits with a message, attached next to the help that describes
  them in prose. The renderer prints only the help, so diagnostics read the same on the command line;
  the language server maps the edits to quick fixes without knowing any diagnostic code.
* **Type definitions** are always unfolded; strict definitions are not folded back in diagnostics.
* **Formula functions.** Every literal object variable of a quote is renamed at each application
  (hygiene, Section 4.8); renamed variables print without the suffix. (`%mode f m̄` on formula functions was removed in C3; it was checked once on
  the body applied to fresh variables; uses are checked by the ordinary moding of the expanded rule.
* **`%infix`.** An operator declared with precedence `p` gets level `10p + 5` on the scale where the
  built-in levels of Section 2.2 are 10 (`;`) … 70 (`* /`); rule heads are parsed above the comparison
  level, so operators with `p ≥ 5` may appear in heads.
* **Layout heuristic.** An argument cannot start a line in column 0. This only matters for error
  recovery: a missing period at the end of an item is reported and the next item is still parsed.
* **Disjunction inside aggregates** (not covered by Section 7.2, which splits disjunctions of rule
  bodies only) is lifted into an auxiliary relation `aux(ī, ō)` with one rule per alternative
  (`obj/transform/Disjunctions.scala`). The inputs `ī` are the disjunction's variables bound before it
  in canonical order; the outputs `ō` are the variables bound by *every* alternative. A variable bound
  by only some alternatives is existential within its alternative. Each rule of `aux` is its
  alternative after the *context* of the call: the formulas before the aggregate that bind the inputs.
  Only the formulas that mention no relation depending on the calling rule's head are kept, if they
  still bind the inputs (issue #1, F1); then `aux` does not depend on the caller and the aggregate's
  negative edge closes no cycle. Otherwise the whole prefix is used and a cycle through the aggregate is
  reported (E0601, `tests/neg/f_aggregate_disjunction_cycle.hgn`). The kept formulas hold wherever the
  prefix holds, so for every binding of the inputs `aux` has exactly the alternatives' answers, and the
  aggregate counts distinct bindings of its variables as usual (issue #1, item B4). The version before
  C3 supplied the inputs by the demand transformation; see the history.
* **Demand relations** are named `c.check` (derived constants, C3; formerly `c^d[m]`), derivation relations `@r` or `@r#i`. Derivation relations
  are output relations; they cannot be referenced in atoms.
* **Primitives.** Integer overflow and division by zero (also for floats) are undefined. Strings
  compare by code point. NaN is never produced by the primitive operations.
* **Input facts** are accepted for relations declared `%input` or `%open`.
* **Dependency graph.** Section 6.4. A body reads the relations of its atoms and, for every binding
  equation `X = c t̄`, the constructors on its value side (an existence check). Comparisons, aggregate
  terms and patterns read nothing. A head depends on what its body reads, and so does every constructor
  whose term it asserts besides its own fact (see the observation on Proposition 8.8 above).
* **Engine.** Identities are `(relation, n)` pairs; relations store tuples in insertion order, so
  old/delta/full windows are id ranges. Hash indexes are created for every set of bound columns that
  occurs in a `Scan`. Bodies are executed by backtracking over the IR; aggregates collect one value per
  distinct binding of the aggregate's local variables (Definition 8.4).

## Termination (issue #2, redesign A1)

The termination check (`obj/check/`: `Termination.scala` the phase, `Constructive.scala` constructive rules
and finite sources, `SizeChange.scala` direction (A), `GuardedInduction.scala` direction (B) with measure
inference, `DemandDriven.scala` its case for `%mode`, `Decrease.scala` and `Intervals.scala` the decrease
reasoning, `TerminationProblems.scala` and `TerminationReasons.scala` the diagnostics, with their reasons as
data) decides statically
that every recursive component reaches a finite fixed point (docs/REDESIGN.md §4). A recursive component
(Section 6.4) needs an argument only if one of its rules is constructive (Definition 10.1, refined below).
There is no escape hatch: `%partial` and round budgets were removed (redesign A3, REDESIGN §4.6); a program
that cannot be shown to terminate is rejected. The check tries, in this order:

1. If a relation of the component (or the relation its demand relations belong to) carries a measure
   `%terminates X (c … X …)`, `%terminates l c`, or lexicographically `%terminates (X, Y) (c … X … Y …)` /
   `%terminates (l, m) c`: guarded induction (B) with the declared measures. The directive is a *hint*:
   it is checked, never trusted, and a failure is E0604 (no fallback to the other direction, so the
   diagnostic speaks about the measure the programmer named).
2. Without a directive: **descent along derivations (A)**, the size-change principle on derivation
   chains (below).
3. Then **guarded induction (B)** with an *inferred* measure: the measures tried are one argument per
   relation (up to four relations of the component, at most 256 combinations) and, for a component with
   a single relation, every lexicographic pair of arguments. The first measure that passes the
   conditions below is used; `--explain-termination` prints it as a directive.
4. Otherwise E0603 (below).

`--explain-termination` prints, for every recursive component, which case applies and the justification
of every recursive step.

### Descent along derivations (A)

**Size-change graphs.** For a rule `H :- …, B, …` of the component and a body atom `B` of the component (a
*premise*), the graph `G(B, H)` has an arc `i → j` from argument `i` of `B` to argument `j` of `H` labelled

* `=` if `h_j` and `b_i` are syntactically equal (up to `as`/ascription), equated by the body, or (integers)
  `b_i - h_j ∈ [0, 0]` by the interval reasoning below;
* `>` (strict decrease) for structural arguments if `h_j` is a proper subterm of `b_i` (unfolding
  variables of `b_i` bound to patterns, as for measures); for integer arguments if `b_i - h_j ≥ 1` (or
  `h_j = x / l`, `l ≥ 2`, `1 ≤ x ≤ b_i`) **and** `h_j` is bounded below: its interval has a lower bound,
  or its variables are bound by finite sources outside the component;
* `≥` (weak decrease) for integers if `b_i - h_j ≥ 0`, or the decrease above holds without a bound;
* `<` (strict increase) for integers if `h_j - b_i ≥ 1` and `h_j` is bounded above (interval or finite
  sources); `≤` (weak increase) if `h_j - b_i ≥ 0` or without the bound.

Arcs only connect two integer or two non-integer arguments. Composition follows the paths
`i → j → k`: `=` is neutral, two decreases give a decrease (strict if one is), two increases an increase,
and a decrease followed by an increase gives nothing (they are measured in opposite directions, so they
never form one thread). The closure of the graphs under composition is checked: **every idempotent graph
`G : p → p` (`G ; G = G`) has a strict arc `i → i`, or the arc `i =→ i` for every argument `i` of `p`.**
Since issue #65 this is decided without the full closure and without a cap (it used to give up, and
reject, above 4000 graphs): only the *weakest* graphs per pair of relations are kept (`G ⊑ G'` if every
arc of `G` is implied by an arc of `G'` between the same arguments), and every kept `G : p → p` is tested
by the local criterion of Ben-Amram and Lee (TOPLAS 2007; Fogarty & Vardi, LMCS 2012, Section 4.1): a
strict arc lies on a cycle of `G`'s arcs of its direction (`=` counts for both), or every argument lies
on a cycle of `=` arcs. That test holds for `G` iff the idempotent test holds for `G`'s idempotent power,
and it is preserved by strengthening, so the verdict is the full closure's (the argument is in
`SizeChange.check`; `ClosureCrossCheckSuite` compares with the old full closure on the corpus and on
generated programs). The idempotent test itself would be unsound with subsumption: the weaker graph that
replaces a bad idempotent one need not be idempotent. `tests/run/t_termination_large_closure.hgn` has a
full closure of 10 085 graphs (formerly rejected) and an antichain of 3.

*Soundness.* Let C be the component, evaluated after the components it depends on, which are finite by
induction over the evaluation order (Definition 8.7; their check is this argument or the finiteness of
non-recursive components). The facts of C are derived by its rules from facts of C and finitely many
facts of earlier components. Define the *depth* of a fact of C as 0 if a rule derives it without a premise
in C, and otherwise as 1 + the least possible maximum depth of the C-premises of a derivation of it.
There are finitely many facts of each depth: by induction, a fact of depth `k + 1` is derived by a rule
whose body valuation is determined by its positive atoms (range restriction) — premises of depth `≤ k`
(finitely many) and facts of earlier components (finitely many) — and arithmetic, equations and
aggregates are functions of that valuation. Suppose C is infinite. Then facts of unbounded depth exist.
Link every fact of depth `k + 1` to a C-premise of depth `k` of a derivation of minimal depth: this is a
forest with finitely many roots (depth 0) and finite branching (finitely many facts of each depth) and
infinitely many nodes, so by König's lemma it has an infinite path `f_0, f_1, …`; its facts are distinct
(their depths are `0, 1, 2, …`), and each `f_{n+1}` is derived from the premise `f_n` by some rule, so
the arguments of consecutive facts are related as the graph `G_n` of that rule and premise says. By
Ramsey's theorem (as in Lee, Jones and Ben-Amram, *The Size-Change Principle for Program Termination*,
POPL 2001, Theorem 4) there are indices `n_0 < n_1 < …` and an idempotent graph `G : p → p` of the closure
such that the composition of `G_{n_k}, …, G_{n_{k+1} - 1}` is `G` for every `k`. If `G` has `i =→ i` for
every argument, `f_{n_0} = f_{n_1}`: a contradiction to distinctness. If `G` has a strict arc `i → i`,
argument `i` of `f_{n_0}, f_{n_1}, …` forms an infinite thread that decreases strictly (or increases
strictly) at every segment and never moves in the other direction. Structurally this is an infinite
descending chain of proper subterms of a finite term: impossible. For integers, every strict step lands
on a value `≥ L` (for decreases; `L` the least lower bound over the finitely many rules, or the least
value of the finite sources), the thread is non-increasing, so it can decrease strictly only finitely
often: a contradiction; increases dually with upper bounds. Hence C is finite. A component whose cycles
are all trivial (`q X Y :- q Y X`: its idempotent graph is the identity) is accepted by the second
alternative.

The integer bound is checked on the *derived* value, which is what the argument needs: the strict steps
land above the bound. `need A :- need N, N > 1, A = N - 1` derives `A ≥ 1`; `need A :- need N, A = N - 1`
is rejected with a help naming the missing guard. The direction is new: before the redesign the
checker rejected these rules (they needed `%partial`), e.g. `check B (bind G X T1) :- check (lam X T1 B) G`
of the hand-written type checker (`tests/run/rd_typechecker.hgn`) and `need` of the hand-written `fib`
(`tests/run/rd_fib.hgn`). It works for data and fact-constructor terms alike: both are finite trees, so
the proper-subterm order is well founded independently of the input. Increases bounded by finite sources
also accept `fib N F :- need N, …, fib A FA, fib B FB, …` read upwards (the head's `N` is larger than the
premises' and lies in the finite set of `need` facts). `tests/run/t_termination_descent.hgn`,
`tests/neg/t_termination_descent.hgn`; `SizeChangeSuite` runs random integer recursions accepted by the
check and asserts that they reach their fixed point.

### Guarded induction (B)

Measures and the conditions of the bottom-up case below are the direction (B) of the redesign: along
every recursive call the call's measure is smaller than the head's, and the head's measure lies in a
finite set (the anchor) — bound by atoms of relations outside the component (relations of earlier
components, constructor facts), by a bounded interval, or by the call's bound plus a bounded difference.
The guard is an ordinary body atom; nothing requires modes. With measure inference, `typed (lam X T1 B) G
(arrow T1 T2) :- check (lam X T1 B) G, typed B (bind G X T1) T2` is accepted with the inferred measure `e`
(the guard `check` binds the head's `lam X T1 B`). The demand-driven case below (moded components)
remains for `%mode` until the demand transformation becomes a library (REDESIGN §7.4, phase C), with
the same measure inference. *Soundness* is the argument of the bottom-up case below (well-founded
induction on the measure, which ranges over a finite set).

### Diagnostics

E0603 (no argument found) names the constructive rule (the invention site), the cycle, why (A) fails (a
cycle of steps, with its rules, whose idempotent graph has no strict self-arc) and why (B) fails (the
first candidate measure that decreases but is not anchored, or that no argument decreases), and a help:
the missing guard when an integer decreases (or increases) without a bound (`` `A` is smaller than `N`
but not bounded below: add a guard such as `A >= 0` ``), otherwise how to make an argument decrease or to
name the measure with `%terminates`. E0604 (a declared measure fails) is unchanged.

### Constructive rules and measures

**Two disciplines.** Growth has two sources, and each existing check belongs to one of them:

1. *Data terms built in recursion or in moded inputs* (structural or measured decrease). A rule that
   builds new values, in its head or as the input of a moded call (the head of a demand rule), can make a
   recursive component infinite. This is the termination problem of logic programs, treated as in
   Twelf's `%terminates` and with level mappings (Apt, Pedreschi; Lee, Jones, Ben-Amram for size
   change): a measure on the arguments, decreasing structurally or numerically along every recursive
   step (bottom-up components, conditions 2 and 3) or along every demand (demand-driven components,
   conditions 3 to 5).
2. *Fact constructors creating facts through closure* (acyclicity of fact creation). A `%fact` term in a
   head asserts a fact of its constructor, which other rules may read; a cycle "rule asserts `c` facts →
   `c` facts are read → rule fires again" is the non-termination of the chase with existential-free but
   term-building rules, avoided by acyclicity conditions on fact creation. Here such a cycle is a cycle
   of the dependency graph (an asserting head constructor depends on the rule's body, Section 6.4), so it
   lies inside one component and is checked by discipline 1: the split rule `c t̄ :- body` of an
   asserting head (Proposition 8.8) is a rule of `c`'s component, and a rule of a fact constructor builds
   its head fact. Across components a fact constructor is a finite source like a plain relation, because
   the split rules complete it in its own component. Data constructors have no facts and no closure:
   they only need discipline 1.

**Constructive rules (Definition 10.1, refined; issue #1, F3).** A rule is constructive if it builds a
constructor term, data or fact, that is not matched in the body, in a head or in a moded input (the head
of a demand rule); also through a head variable bound by a binding equation with a data term
(`num X :- num Y, X = s Y` builds `s Y`, `tests/neg/t_termination_equation_ctor.hgn`; an equation with a
fact constructor only checks a fact and builds nothing). Clause (a) of Definition 10.1 counts every
constructor term of a head that is not matched in the body (issue #1, B9: the arguments themselves
included). The implementation counts such a term only if it can take infinitely many values over the
evaluation of the component: it is *not* constructive when it is ground (`d X red :- d X _`, `e (mk 1)`)
or when each of its variables is bound by a *finite source*: a positive body atom outside the component
of a relation that is not a fact constructor or fact struct (`e X (mk Y) :- e X _, b Y`); a generated
guard `(c Z̄ as X)` over a data constructor destructures `X` and binds finite variables if `X` is finite
(`Termination.finiteVars`). If the head's relation is a fact constructor, the head term itself counts
too (its fact is a term): `s (s N) :- s N` is constructive. Clauses (b) (a matched fact lifted into the head) and (c) (arithmetic in the
head or computing a head variable) are unchanged.

*Soundness.* The argument for components without constructive rules was: their facts consist of terms
that exist before the component is evaluated, a finite set, so the fixed point is finite. With the
refinement, the terms a rule can construct are the instances of its non-constructive head terms. A
ground term has one instance. A term whose variables are bound by finite sources has one instance per
valuation of those variables, and each such variable is a subterm of a fact of such a relation (or the
fact itself, for `as` variables). Those relations belong to earlier components, which are complete when
this component is evaluated (Definition 8.7) and finite by induction over the evaluation order (recursive
components are checked here; others are finite in their inputs). Plain
relations only get facts from their own rules, so they do not grow later. So every rule constructs terms
from a fixed finite set, and the component's facts consist of the existing terms plus that set: still
finite. Fact constructors and fact structs count as finite sources outside the component like plain
relations: their facts come from their own rules and from the split rules of heads asserting them
(Proposition 8.8), all evaluated in their component; a later assertion only repeats a fact of a split
rule. (Before the repair they were excluded, since `d (s (s N)) :- s N` created `s` facts after `s`'s
component; now that rule is split into `s (s N) :- s N` and rejected in `{s}`,
`tests/neg/t_termination_ctor_source.hgn`.) The anchor condition below uses the same finite sources. Variables bound only by
equations, arithmetic or aggregates keep the term constructive (conservative). In the measured cases the
conditions "rules of unmeasured relations are not constructive" use the same notion; there "only copy
existing terms" becomes "construct terms from a fixed finite set", which the arguments below need in the
same way (finitely many facts per round, finitely many terms overall).
`tests/run/t_termination_finite_ctors.hgn` shows the accepted cases.

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
   it lies in a finite set (`L ≤ h_j ≤ B`). A slot is bounded if its variables are bound by finite
   sources outside the component (a finite set: those relations are finite by induction over the
   evaluation order), or by its interval, or by the call's slot (bounded likewise) plus a bounded
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

*The demand-driven case of guarded induction (moded components) was removed with relation modes in C3;
it is in the history.*

**Diagnostics.** E0603 names the constructive rule, the cycle through the component, and a measure that
would be accepted (single positions per relation, or a lexicographic pair for a single relation, found by
running the check). E0604 points at the call (or the demanded call) that fails, labels the
head's or caller's measure, says which slot of the measure fails and whether the decrease or the anchor
is missing, and suggests the missing comparison. Components with a cycle through negation
are skipped (E0601 is reported).

**Not covered.** Measures through non-linear arithmetic other than division by a literal, multiset
orders, declared measure functions, anchors through finite (non-recursive) types, and components that
need (A) for some relations and (B) for others at once (a hand-written demand relation in the same
component as its answer relation, which happens when demand depends on answers; the generated demand of
`%mode` is covered by the demand-driven case). Argument permutations are covered by (A).

## New meta level (redesign Phase B)

The meta level of `docs/REDESIGN.md` §6 is `hugin.core`; since B3c it is the only one. The phases
`elaborate` (the core elaborator, with the prelude and the imported files) and `stage` (the handover of
the staged object items to the object level) come after `parser`, and every object-level phase from
`directives` on runs unchanged. `--print-after elaborate` prints the elaborated program (meta definitions
with the inserted quotes `⟨⟩`, splices `$` and implicit arguments) followed by the staged object items.
(While it was developed, B1–B3b, the old meta level was the default and this one ran behind the hidden
flag `--new-meta`; the decisions below that mention the flag or "the old pipeline" describe that time.)

### Architecture

The design follows Kovács's elaboration-zoo (normalisation by evaluation, bidirectional elaboration,
metavariables with higher-order pattern unification and pruning, implicit arguments) and his staged
elaborator for two-level type theory (*Staged Compilation with Two-Level Type Theory*, ICFP 2022).

| file | contents |
|---|---|
| `core/Syntax.scala` | core terms `Tm` (de Bruijn indices), stages `S0` (object) / `S1` (meta), universe levels |
| `core/Value.scala` | values: closures, neutrals (`Rigid`/`Flex` with spines of applications, splices, projections) |
| `core/Evaluation.scala`, `Readback.scala` | `eval`, `force`, `quote`, `nf`, `zonk` |
| `core/Renaming.scala`, `Unification.scala` | partial renamings, pruning, eta-expansion of metas; pattern unification, conversion |
| `core/Levels.scala` | universe level constraints (difference constraints, least solution) |
| `core/Core.scala` | the state: globals, metas, levels; `undoOnFailure` |
| `core/Printing.scala` | printing in surface notation |
| `core/Staging.scala`, `NewMeta.scala`, `CorePhases.scala` | staging of object items, the driver, the compiler phases `elaborate` and `stage` |
| `core/ObjForm.scala` | the forms of object syntax (one inert core node `Obj`): formulas, `as`, ascriptions, projections, updates, aggregates, unions, bound columns, positions |
| `core/handover/*` | B3: staged object items to `obj.Trees` (`ObjectSymbols`: object constants to `TypeSym`/`RelSym`; `ObjectTerms`: terms and formulas; `Handover`: the `ObjProgram`) |
| `core/CaseTree.scala`, `Matching.scala` | case trees of functions defined by clauses, their reduction with memoisation |
| `core/elab/*` | the elaborator, one trait per concern: `Bidirectional` (dispatch), `Universes`, `PiTypes`, `Applications` (implicit insertion), `Records`, `Operators`, `Coercions` (stage inference), `Names`, `Contexts`, `Declarations`, `Items`, `ObjectItems`, `ElabErrors`; for B3 `ObjectDecls` (structs, refinements, edges, cycles), `ObjectCode` (object-only forms, positions, deferred object typing), `NamedPatterns`, `DataConstructors`, `ObjectProblems` (typed diagnostics); for B2 `Inductives`, `Patterns`, `SplitProblem` (split contexts, index unification), `Clauses` (case trees, coverage), `SizeChange` (termination) |

Every elaboration error is a diagnostic (`E09xx`, plus `E0101`/`E0102`/`E0307`); an item with an error is
dropped and elaboration continues with the next one.

### Decisions (B1)

* **Universes.** `type` is the universe of object types (2LTT's U₀). It is classified by itself; this is
  harmless because the object level is simply typed: there are no object lambdas (E0908) and object
  arrows cannot range over `type` (a binder over object types is always a meta binder, `(A : type) -> …`
  is `(A : ⇑type) -> …`). `Type` is the meta hierarchy: every occurrence gets a fresh level variable; the
  constraints (`Type l : Type (l+1)`, Π and record formation, cumulativity) are difference constraints
  kept satisfiable incrementally, with their least solution (`Levels`). Cumulativity is a coercion
  (contravariant in Π domains), as in Kovács's subtyping coercions; unification of universes equates
  levels. A meta whose type is a universe `Type l` gets the constraint that its solution lives in `Type l`
  (unification alone would not check it under cumulativity). Level variables are global to a program: no
  universe polymorphism (a definition is used at one level, which cumulativity makes rarely restrictive).
  `Type : Type` is rejected (E0904).
* **`⇑type` is small.** `⇑A : Type₀` for every object type `A`, also for `A = type`: object types carry no
  meta-level computation, so a signature whose components are object types and relations
  (`{ node : type, edge : node -> node -> rel }`) is in `Type₀`, and only signatures with meta-type
  components (`{ t : Type }`) are in `Type₁`. REDESIGN §8.4 said `Type₁`; this is a refinement.
* **Stage inference.** As Kovács: every term has the stage of its type's universe; checking against `⇑A`
  checks object code under a quote; `coe` adjusts stages (quote, splice, `⇑` on types), coerces functions
  by eta-expansion (so a relation `⇑(A -> rel)` can be passed where a formula function `⇑A -> ⇑prop` is
  expected) and falls back to unification. Explicit forms: `$t` (splice, REDESIGN §6.9) and `⇑A`.
* **Base types and literals (Q2).** A base type written where a meta type is expected is the meta
  primitive (`int -> int` checked as a meta type is a function on compile-time integers, as the current
  `Prim` types); `⇑int` is object code of type `int`. A meta primitive value used as object code is
  persisted as a literal (`k : int = 6 * 7.  q k.` stages to `q 42.`); `$k` does the same explicitly.
  Literals take the type and stage expected; inferred literals are meta values. Compile-time arithmetic
  uses the shared primitives (`obj/Prims`); an undefined result (overflow, division by zero) that reaches
  object code is E0909.
* **Arrows.** An arrow ending in `rel` is an object relation type wherever it is written (in a signature,
  `edge : node -> node -> rel` is `⇑($node -> $node -> rel)`). An arrow checked against `Type` is a meta
  function type: `item -> prop` is the formula-function type `⇑item -> ⇑prop`. A relation used as a type
  is its fact type (`listed : item -> rel`).
* **Declarations** are classified by inferring their type (REDESIGN §6.2): an object constant (object
  type, constructor, relation) if the type is one, otherwise the type is checked as a meta type (so
  `f : int -> int.` is a meta function, not an object constructor into `int`). Free uppercase variables of
  a declaration are implicit binders; when the type of such a binder is not determined before it is used
  as a type, it is tried as a meta type first and then as an object type (`vcons : A -> vec A N -> …` vs.
  `cons : A -> list A -> list A` with `list : type -> type`); the failed alternative is undone
  (`Core.undoOnFailure`). Head parameters `list A : type.` range over object types. A declaration with
  parameters or implicit binders is a meta-level constant (`list : ⇑type -> ⇑type`, `nil : {A : ⇑type}
  -> ⇑$(list A)`): families are meta functions, memoised in B3.
* **Order.** Meta and object declarations may be written in any order: an item that refers to a name
  declared by a later item is retried after it (`Items.elabInDependencyOrder`). Rules and queries are
  elaborated after all declarations.
* **The object level in the core** is typed by unification, without subtyping, unions or refinements:
  enough for staging and implicit arguments. Object typing proper stays with `obj/typing/ObjTyper` (B3
  hands it the staged items). The variables of rules are bound implicitly at stage 0 with unknown object
  types, which may stay unsolved. A constructor application used as a formula is an atom of the
  constructor's relation (REDESIGN §3.2).
* **Staging** of an object item is its normalisation (`$⟨t⟩ = t`); what remains must be object code, or
  E0909 reports the stuck meta code (a postulated meta function, an undefined primitive).
* **Not yet (B3):** module bodies, imports, signatures with requirements (`%complete`, `%mode`),
  aggregates, `as`, record updates, unions, subtyping edges, hygiene of object variables in formula
  functions, generativity and memoised families (E0907 where the syntax is accepted).

### Decisions (B2)

* **Clauses.** `f p̄ = e.` (and `f X̄ = e.` after a declaration `f : A.`) are clauses of the declared
  function `f`; the parser produces `Clause` items in the new syntax when a definition head is not just
  variables. A declaration with clauses declares a function; clauses are elaborated after all
  declarations, so functions may be (mutually) recursive and may use every declaration of the module.
  Patterns are uppercase variables (bound once), `_`, constructors applied to their explicit arguments,
  and natural-number literals of a nat-like type. Implicit arguments are not written in patterns; the
  names of the function's implicit binders (`A`, `N` in `head : vec A (suc N) -> A`) are in scope in the
  right-hand side unless a pattern variable shadows them. The arguments up to the last explicit pattern
  are matched; the right-hand side is checked against the rest of the type.
* **Inductive families.** A meta declaration without definition or clauses is classified by its type:
  `T : Δ -> Type.` is an inductive family, `c : Δ -> T ū.` (with `T` a family of the module, fully
  applied) one of its constructors, anything else a postulate (kept for now: postulates are stuck at
  compile time, and E0909 reports them when object code depends on them). All arguments of a family are
  indices: there is no separate notion of parameters, dependent matching unifies them. Constructors are
  checked for strict positivity (E0913) and predicativity: their argument types must live in the
  family's universe, which levels inference turns into constraints (`small : Type. mk : Type -> small.`
  is accepted with `small : Type₁`, but `mk small` is then a universe inconsistency).
* **Case trees** follow Cockx & Abel (ICFP 2018), without copatterns and without the restrictions of
  `--without-K`: a split context whose variables may be *solved* by index unification (deletion,
  solution, injectivity, conflict, cycle), equations `term / pattern` per clause, splitting on the first
  constructor pattern of the first applicable clause. Constructors whose indices conflict get no branch
  (impossible cases need no clause); a branch without clauses is accepted only if some variable has no
  applicable constructor (an empty split, as `lookup vnil i` with `i : fin zero`), otherwise it is a
  missing case (E0911, which prints the missing pattern). Unification problems that are neither
  solvable nor impossible (an index `plus N M` against `zero`) are reported (E0915) rather than
  postponed. A clause that never reaches a leaf is unreachable (W0006).
* **Evaluation.** A function applied to its arity of arguments runs its case tree; a split on a neutral
  leaves the application neutral, and `force` retries it later. Applications to closed arguments are
  memoised by their normal forms (sound, since meta functions are total and pure); this makes
  `fibm (suc (suc N)) = fibm N + fibm (suc N)` linear, so `fib 90 (fibm 90).` stages to
  `fib 90 2880067194370816120.` (REDESIGN §8.2).
* **Termination** uses the size-change principle (Lee, Jones & Ben-Amram) over the constructor-subterm
  order, implemented on its own in `core/elab/SizeChange.scala` (a call graph with size-change matrices,
  closed under composition; every idempotent self-loop needs a strict decrease). It accepts structural,
  lexicographic (Ackermann), mutual and permuted recursion. The object level's checker
  (`obj/check/Termination.scala`, reworked in Phase A) solves a different problem (derivations of
  facts); sharing the closure computation is possible later.
* **`where` blocks** (designer addition to §6.4). Parsing: in the new syntax `where` is a keyword. After
  the right-hand side of a clause starting at column `c`, `where` opens a block of items (definitions,
  signatures, clauses); the block takes every following item that starts at a column greater than `c`
  and ends before the first item starting at column `c` or less, at a `}` or at the end of the file. The
  first binding may follow `where` on the same line. Each binding ends with its own period; the last
  one ends the clause (no period before `where`). Nested blocks follow the same rule relative to their
  binding's column. A definition head `f X̄ = e where …` with only variables is a clause as well.
  Elaboration (`core/elab/Where.scala`), at each leaf of the clause, in order: `x = e.` and `x : A = e.`
  are let-bound (`Let` in the leaf's body); a local function (`f : A.` and the clauses after it) is
  lambda-lifted to a hidden global whose type abstracts over the bound variables of the leaf's context
  (defined ones are let-bound in its type, and every name in scope is re-defined in its clauses from
  its arguments), elaborated by the clause compiler, and its name is let-bound to the global applied
  to the context; an irrefutable pattern binding `c x̄ = e.` becomes one lifted selector function
  `sel (c x̄) = xᵢ` per name, so that coverage rejects refutable patterns (E0911), and fields whose
  types depend on other fields are not supported (E0915). Termination: calls through the let-bound
  names of local functions are calls of the lifted functions. Every function's termination is checked
  as soon as its case tree exists, and a rejected function's case tree is removed, so that no
  possibly non-terminating function is ever evaluated during elaboration.
* **Literals (Q2).** A literal checked against a nat-like family (exactly a constant constructor and one
  with a single recursive argument, `zero`/`suc`) is the unary numeral `suc (… zero)`, also in patterns;
  otherwise literals are meta `int`/`float`/`string` values (or object literals at stage 0). Meta `int`
  has no conversion to `nat` yet (a function by clauses on `nat` gives the other direction).

### Decisions (B3a: the handover to the object level)

* **Object syntax is one core node.** `Tm.Obj(form, args)` / `Val.Obj` (`core/ObjForm.scala`) hold the
  object-only forms: formulas (`,` `;` `not`, comparisons), `_`, `as`, ascriptions, projections and
  updates of facts, aggregates, union types, bound column types, and positions. Evaluation, read-back,
  unification and renaming treat all forms alike (object code is inert data), so the B3 forms added no
  cases to the core's algorithms; the former `Compare`/`And`/`Or`/`Not`/`Wild` nodes were folded into it.
* **Positions.** An object term or formula elaborated from a tree is wrapped in `Obj(Loc(span), t)`
  (`ObjectCode.located`; types, relations and constructors are not). Evaluation keeps positions, so the
  staged program carries them into `obj.Trees` and the object-level diagnostics point where the old
  pipeline pointed (also into the bodies of meta functions that produced the code). Unification and
  application look through positions; the innermost position wins (`(X)` has the position of `X`).
* **Object typing is deferred** (the risk noted for B3). [Superseded by #56: object typing runs in the
  core at the end of each scope; see "Typed object code (#56)".] The core unifies object types where it can
  (that solves implicit arguments and the types of rule variables) but never rejects object code for its
  object types: between two object data types that do not unify, `Coercions.coe` keeps the term
  (`coeObjectData`); literals in object code are object literals of any type; arithmetic operand types
  are not checked at stage 0; projections get the column's type if the fact type is known, otherwise an
  unknown one. Subtyping, unions, refinements, fact types of relations, labels of projections are the
  object typer's (`ObjTyper`), which sees the staged program. What the core does check is the *shape* of
  object code: stages, arities (a relation applied as a function), labels of named patterns (they need
  the columns), data constructors used as relations (E0406, until C3 removes the data/fact split).
* **Object declarations.** `GlobalKind.Object(ObjDecl)` classifies object constants (open type,
  refinement `a : type <: b.`, relation, constructor with its `%fact` flag, struct `s : type = { … }.`, a
  relation whose fact type is `s`); `τ <: a.` is an `EdgeItem`. A constructor or struct used as a type
  denotes its fact type, as a relation does. Bound column types `min τ` / `max τ` are allowed in the columns
  of relations and constructors (the object level's `BoundColumns` validates them), elsewhere E0605.
* **Cycles between object declarations** (`abs : (body : term) -> rel.  term : type = var | abs.`):
  relations, structs and constructors (whose result is a `: type` declaration of the module) are declared
  *pending* before the declarations are elaborated (`ObjectDecls.predeclare`): a pending constant can be
  used as a type (its fact type) but not applied, which retries the item after the declaration. This is
  the only mutable part of a global (`GlobalEntry.ty`), and only during the declaration phase.
* **Compile-time arithmetic in object code.** Arithmetic whose operands are both meta primitives (and not
  both literals) is computed at compile time and persisted (`k = 42.  q (k + 1).` stages to `q 43.`), as
  the old typer did; an undefined result reaching object code is E0909 (the old pipeline reported E0209
  at the meta definition already; meta definitions are values, evaluated where they are used).
* **The handover** (`core/handover`): object symbols are created in source order (the object level
  orders members of closed types by symbol id), then their columns are translated; rules, queries,
  edges and directives are staged (`nf`, checked by `Staging.objectCode`) and translated. Wildcards
  become `_#1`, `_#2`, … per item in order of occurrence, as the old typer named them. An item whose
  staged code does not have the shape of an object item is reported (E0202, E0909) and left out.
* **Diagnostics** of object code found by the core are typed problems (`ElabProblem`, docs/DIAGNOSTICS.md)
  with the old typer's wording where the old typer reported the same concept (W0002, E0301, E0302, E0306,
  E0307, E0406, E0605, E0701, E0404); an item stops at its first error (the old typer reported all errors
  of a rule).
* **Acceptance.** `PipelineParitySuite` runs every golden program of `tests/run` and `tests/neg` through
  both pipelines; 63 programs produce the same output (results, diagnostics, exit code). The others use
  families, modules, functors, formula functions or imports (B3b) or diagnostics of the old typer that
  the new meta level reports differently; each is listed with its reason.

### Decisions (B3b: families, modules, formula functions, imports)

* **Families are memoised.** A declaration with type parameters (`list A : type = nil | cons A (list A).`,
  `len A : list A -> int -> rel.`) is a `GlobalKind.Family`; an application to closed object types is
  normalised (positions stripped) and memoised to one *instance*, a global named after its arguments
  (`len[int]`, `cons[list[int]]`), so the object level sees the same names as before. Unification relates
  a family application with its instance (`core/Families.scala`). Rules over a family's parameters are
  *generic* (`RuleItem.generic`) and staged once per instance used, through a worklist that also follows
  instances used by other instances (`handover/Generics.scala`); a rule whose recursion needs a new
  instance of its own family is polymorphic recursion (E0205). Struct families take their type arguments
  explicitly in types and implicitly in terms (`pair 1 "x"`).
* **Formula functions** (`cheap : item -> prop = [I] I.price < 10.`, or clauses) are meta functions
  into `⇑prop`; their object-typed and base-typed parameters are object code (`int -> prop` is
  `⇑int -> ⇑prop`). Clauses become one disjunction `[x̄] ⟨(x̄ = t̄₁, ψ₁) ; …⟩`. Variables local to a
  clause are bound by `Tm.Fresh`, which evaluation renames per use (`X#1`, `X#2`): hygiene. `%mode` on a
  formula function is E0501 (it has no extension of its own); a formula function without clauses is
  always false (W0005).
* **Modules are generative records.** A body `{ items }` is `Tm.Module(body, env)`: its declarations
  and definitions are members, its object items are elaborated in the context of all members. Evaluating
  a body whose environment is closed creates fresh object constants for its object members — once per
  (body, closed environment, item that evaluates it) — and the handover stages its items (`Modules.scala`,
  `ModuleInstance`). Instances are named after the definition that created them (`hops.r`), `_m1` for an
  anonymous one, with `#k` suffixes when a name repeats. A definition is evaluated once, so all uses of
  `m = f x.` share the instance; two applications `f x` in two definitions are two instances
  (generativity). A functor application records its origin (`Tm.Trace`) for diagnostics ("in
  application of `f`").
* **Signatures are record types with requirements.** `%complete r`, `%mode r …` and `%fact c` in a
  signature are `SigReq`s of `Tm.RecTy`. Ascription is transparent (the record type is the type; the
  value keeps its members). A requirement is recorded where a functor is applied (`Tm.Require`, evaluated
  to a `RequirementUse`) and checked by the object level on the staged program (E0208), except `%fact`,
  which the core checks (E0204). Negation over a parameter's relation needs `%complete` (E0210).
* **Imports.** `%import "f"` is the record of `f`'s declarations (`ImportedModule`); its object constants
  are qualified by the file's qualifier (`shapes.shape`). Libraries are elaborated in import order (since
  B3c as a memoised chain); the prelude (then `<stdlib>/prelude-core.hgn`, the old prelude in the new
  syntax; the prelude since B3c) is the parent scope of every file. Without the prelude, `int`, `float`
  and `string` are not in scope.
* **`mod`** was accepted as an alias of `Type` (signatures are record types in `Type`) until B3c removed
  it and rewrote the tests that used it.
* **Diagnostics that changed** (with `--new-meta`; the `.check` files change when B3c makes the new meta
  level the default):
  * `run/a10_meta_applicative`: the program is printed after `stage`; there is no `monomorphize` phase.
  * `run/f_demand_per_call`, `run/t_termination_explain`, `run/t_termination_len_callers`: positions in
    the prelude were `<stdlib>/prelude-core.hgn` until B3c made it the prelude (same lines; unchanged now).
  * `neg/a11_stage_overflow`: meta definitions are values; an overflow is reported where the value reaches
    object code (E0909), not at the unused definition (E0209 retired for the new meta level).
  * `neg/classification`: `r : int -> rel = 5.` is a type mismatch (E0901): a meta definition of a
    relation-valued type is allowed (`r : int -> rel = m.r.`).
  * `neg/names`: definitions are elaborated in dependency order, so a forward reference is accepted; only
    a self-reference is E0105.
  * `neg/typedefs`, `fix/abbrev`: type definitions with parameters are meta functions; strictness (E0106)
    and `%abbrev` are retired.
  * `neg/interfaces`, `neg/meta_types`: signature and meta type errors in the new meta level's words
    (E0204 naming the field, E0906 for a missing member, E0901/E0905 for argument mismatches); signatures
    are printed as record types (`{ node : ⇑type, edge : ⇑($node -> $node -> rel) }`).
  * `neg/stage`: E0902 replaces E0201; `not` over a formula function's expansion is E0202 with a note.
  * `neg/f_nil_ascription_help`, `neg/polymorphic_recursion`: E0206 has a generic help.
  * `neg/f_data_ctor_relation`: the label at a functor parameter's declaration is not shown.
  * `repl/*`: REPL sessions are composite programs, routed through the new meta level in B3c.
* **Acceptance.** With `HUGIN_NEW_META=1` every golden passes except the ones listed above;
  `PipelineParitySuite` compares the two pipelines on all other golden programs (the listed ones are
  excluded with their reasons).

### Decisions (B3c: the switch)

* **One meta level, one syntax.** The parser always accepts the meta level's syntax (clauses, `$`, `⇑`,
  implicit binders, `where`); `mod` is gone (signatures are record types in `Type`); the prelude is the
  former `prelude-core.hgn` (`<stdlib>/prelude.hgn`, same lines as before the redesign). Deleted: the
  namer, the typer (`meta/typer/*`), MetaEval, Monomorphize, the meta trees and symbol tables, the
  imports phase (the import graph is loaded by `elaborate`), and in the object level the forms that only
  existed before meta evaluation (`Splice` terms, formulas and types, type parameters `TParam`, `OType.Param`
  and `OType.Meta`); `RelSym.instanceOf` stays, for the display names of instances (`len` for `len[int]`).
* **Elaboration in parts** (`core/ProgramElab`). A `Core` can be *forked*: a copy sharing the globals
  (an elaboration only adds globals, it never changes the ones it was forked from), with copies of the
  metas, universe levels and memo tables. The prelude and the imported files form a chain, each elaborated
  in a fork of the core before it; the program's declarations (everything but rules, queries and
  directives) in a fork of the chain's; each object item on its own in a fork of the declarations'; the
  program is assembled in a last fork, where the items are moved in: the family instances an item
  created are the instances at the same arguments there (`Tm.rename` maps the ids), the metas it left
  (the types of object variables) are created again. An item that created module instances or universe
  levels of its own is elaborated again in the assembled core instead. The direct compilation and the
  query database run the same parts, so incremental results equal those from scratch by construction.
* **Positions are spans.** What the core used to compute eagerly from positions (where a module instance's
  constants and items are placed) is kept as a span (`GlobalEntry.placedAt`, `ModuleInstance.placedAt`)
  and turned into a position at the handover, so results computed for an item stay valid when the item
  moves. Files are ranked explicitly (`Core.rankFile`): the prelude, the imported files, the program's
  files in the order of their declarations, then those of the object items.
* **Prelude names.** A prelude object constant that the program redeclares is named `prelude.n` by the
  handover (`ObjectSymbols.objectName`), no longer by the elaboration of the prelude, so the prelude's
  elaboration does not depend on the program.
* **Tooling** reads a new `SemanticIndex` (symbols are `compiler.Sym`: name, kind, the span of the name
  and of the declaration): the elaborator records references (names, parameters, fields through paths:
  record types carry the positions of their fields' declarations, `Tm.RecTy.decls`), declarations with
  their descriptions, members, column labels and scopes (`elab/Tooling`); staging records quotes, splices
  and persisted values (an observer in `eval`, active while the handover stages items) and family
  instances. Hover descriptions show declared types as written and inferred types in the printer's
  *plain* mode, which shows splices of names and paths as the names and `⇑type` as `type`.
* **Closed type instances.** An instance of an open type family comes with the instances of its
  constructors at the same arguments (`option[int]` with `none[int]`, `some[int]`), so input facts can use
  constructors the program never applies, as monomorphization did.
* **Diagnostics.** Every diagnostic is a typed problem (`ElabProblem`, `TypeProblem`, `ClauseProblem`);
  `Legacy` is gone and `Diagnostic.code` is a `Code`. The REPL's own errors are E1101, a crash reported
  by the language server E1102. An item stops at its first error; uses of a name whose declaration was
  dropped (also in an imported file) are not reported again. Classification (E0103: a declaration whose
  result is a base type or `type`, `%builtin` outside the definition of a base type), self-reference
  (E0105), a data constructor passed for a relation (E0406), duplicate declarations (E0102) keep the old
  pipeline's wording. New: E0916, the binders of a declared type used in its definition
  (`f : (x : A) -> B = e.`), with a machine-applicable rewriting to `f (x : A) : B = e.`; an untyped
  parameter of a definition `f X : A = e.` has an inferred type (of a type definition, an object type).
* **Aggregates.** The result of `count` is an `int` and that of `sum`/`min`/`max` has the aggregated
  term's type in the core already, so implicit type arguments that depend on it are solved (found by the
  generated fuzz suite: `V = cons N nil` with `N = count { … }`).
* **Changed `.check` files** (all reviewed): those listed for B3b, now with the final prelude path, plus
  `run/a10_meta_applicative` (`--print-after stage`; `put[int]` is listed where `box[int]` is first
  used), `neg/labels`, `neg/requirements` and `neg/f_data_ctor_relation` (columns moved by `mod` →
  `Type`), `neg/core_e0906_field` and `repl/imports` (a help naming a similar field), `neg/core_e0907_unsupported`
  (the final wording), `repl/files`, `repl/session` (REPL errors have the code E1101), the `core_*`
  goldens without the flag; `fix/abbrev` is deleted (E0106 and `%abbrev` retired), `fix/type_binder_params`
  and `neg/e0916_type_binder` are new.
* **Tests.** Deleted with the old meta level: its unit suites (`meta/*`), the parity suite (two pipelines
  no longer exist). Rewritten: the incrementality suites (`ItemQueriesSuite`, `LibraryQueriesSuite`, the
  REPL's counts) for the granularity above; tests that relied on forward-reference errors (E0105) now
  check that a definition may come after its uses.

### Open issues (after Phase B, for Phase C)

* Finer incrementality: an object item depends on all declarations of its file; per-declaration
  dependencies would need item results that survive a re-elaboration of the declarations (globals keyed
  by stable names rather than ids).
* Not supported (E0907): refinements and families in module bodies, inline module bodies in object
  items are re-elaborated at assembly (correct, not incremental).
* An implicit type argument that only the object typer could determine (the type of an object variable
  constrained by nothing in the core) stays unknown and is reported at staging (E0909), not as E0206.
  [Resolved by #56: object typing solves it, or it is E0206 at the item.]
* E0202's concepts (shape, stage, unbound aggregate) still share a code; "no member" is E0906.
* Phase C: reflection (§6.8), quoted patterns and `$`/`$..` holes (§6.9) (done in C1, see "Reflection"
  below), directives as meta functions
  (C2), `%demand` in the prelude and the removal of relation modes and the data/fact split (C3).

## Reflection (redesign Phase C1)

Object syntax as data (REDESIGN §6.8) and quoted patterns with holes (§6.9). The reflective types are
ordinary inductive types of the prelude; the compiler adds reification (syntax → data, in expressions
and patterns), splits by identity in case trees, and reflection (data → syntax → elaboration).

| file | contents |
|---|---|
| `syntax/QuoteSyntax.scala` | holes `$x`, `$..xs`, `$f[t̄]`; lists `[ē]`, `e :: es`; rules as expressions `(h̄ :- b)` (since #76: quotes `'{ … }` instead) |
| `core/elab/Reflective.scala` | the prelude's reflective globals, the kind of an expected type (`RKind`), data constructors |
| `core/elab/Quotes.scala` | when syntax is quoted, its analysis (`Q`), reification in expressions, meta lists (since #76: the analysis; `QuoteTerms.scala` the rest) |
| `core/elab/QuotedPatterns.scala` | quoted patterns (`Q` → `Pat`), higher-order holes |
| `core/elab/Reflection.scala` | data → syntax with resolved symbols (`SymRef`), items `$e.`, formulas and terms in object code |
| `core/elab/ReflectionProblems.scala` | E0917 (invalid quoted syntax), E0918 (reflection failure) |

### The reflective types (prelude)

| type | constructors |
|---|---|
| `seq A` | `snil`, `scons` (`[]`, `[a, b]`, `x :: xs`), with `sappend` |
| `sym` | none: `%builtin symbol`; its values are object constants, compared by identity (`⟨typed⟩` when printed) |
| `term` | `tvar string`, `tbound index`, `twild`, `tint`, `tfloat`, `tstr`, `tapp sym (seq term)`, `tarith arith_op`, `tneg` |
| `formula` | `fatom sym (seq term)`, `fcmp cmp_op`, `fnot`, `fconj`, `fdisj`, `fagg agg_op x t φ` |
| `rule` | `horn (seq formula) (seq formula)`: heads and body conjuncts |
| `item` | `irule rule`, `iquery (seq formula)` |
| `module` | `seq item` (a definition) |

`openT k w t` / `openF k w φ` (by clauses in the prelude) replace the bound variable with index `k` by
`w`; `index` is nat-like (`izero`, `isuc`), so literals work in patterns.

### Decisions (C1)

* **Names.** Uppercase names are variables in Hugin, so the types of §6.8 are lowercase: `term`,
  `formula`, `rule`, `item`, `module`, and `List` is `seq` (with the list syntax above; `list` is the
  prelude's object list). The constructor of `rule` is `horn`. A program may shadow every one of these
  names (the reflective machinery finds the prelude's by name in the prelude's scope, not the program's).
  There is no `Var` type: variable names are `string`s. `Decl` is not there yet: reflected declarations
  create object constants, which C2 (directives adding declarations) and C3 (`%demand` declaring
  `r.check`) need and will design; `irule` and `iquery` are the items for now.
* **Untyped reflection** (Q5, first version; [#56 added `quoted A` and typed quotes and holes, see "Typed
  object code (#56)"]): `sym` is one type for all object constants (not
  `⇑(τ̄ → rel)`), `term` is untyped; reflected code is re-checked. Data refers to object constants by
  symbol, so it cannot name undeclared ones, and matching is by symbol: a pattern on `edge` does not match
  the `edge` of a module (`m.edge`), nor a program's `edge` that shadows the one in scope where the
  pattern is written.
* **What is quoted.** [Superseded by #76: only the content of a quote `'{ … }` (and a directive's
  arguments) is quoted; see "Explicit quotes (#76)".] Where a reflective type is expected, syntax is quoted if it is object syntax of that
  kind: an object constant (also a path `m.r`) or a hole `$r` applied to arguments, a rule `(h :- b)`, a
  formula (`,` `;` `not`, comparisons, aggregates `X = k { … }`), arithmetic or a literal for a term, a
  hole. Anything else is meta code of the reflective type (`R`, `guard R`, `fatom S Ts`, list syntax),
  so in a quoted formula position a meta variable needs its `$` (`($Pre, $F)`). Inside quoted syntax a
  plain uppercase variable is an object variable: in an expression `tvar "X"`, in a pattern any object
  variable (patterns are linear: two occurrences are not compared); `_` is the object wildcard `twild`
  in a term position and matches anything in a formula position; `$_` matches anything. A single atom
  where a rule is expected is a fact (`horn [a] []`); a rule where an item is expected is `irule`.
  `as`, ascriptions, projections, `with`, named patterns have no representation (E0917).
* **Sequences.** `$..Xs` stands for the arguments of an atom, the heads or body conjuncts of a rule, or
  the elements of a list. In an expression it may be anywhere (`sappend` joins); in a pattern it must end
  its sequence (E0917). A list element may be a rule whose body extends to the closing `]`
  (`[h :- a, b]` is one rule, as in §6.8); several rules with bodies are parenthesised. [Superseded by
  #76: rules in lists are quotes, `['{ h :- a, b }]`; `$..` is a hole of quotes only.]
* **Aggregates are locally nameless.** In `X = k { t | φ }`, if `t` is a variable `V`, `V` is bound: its
  occurrences in `t` and `φ` are `tbound` indices (one binder per aggregate). Reflection names it afresh
  (`V#1`): the variable is local to the aggregate even where the source used the same name outside it.
  Other variables are names (Datalog's grouping variables are the shared names). A higher-order hole
  `$F[V]` in a pattern needs `V` bound by an enclosing aggregate; it binds `F : term -> formula`
  (`term -> term` in a term position) as a definition `F = [w] openF i w F#body` added to the clause's
  `where` block, with a pattern variable for the body. In an expression `$F[t̄]` is `F` applied to the
  quoted terms.
* **Matching by identity.** Quoted patterns elaborate to constructor patterns over the reflective types,
  so coverage (E0911), termination (E0912) and index unification apply unchanged. Object constants and
  literals have no constructors; a pattern on them is `Pat.PAtom`, and the case tree splits with
  `CaseTree.SplitAtom`: a branch per value the clauses name and a default branch with the clauses that
  do not constrain the variable (as for literal patterns in ML). A split on a value that is not
  canonical yet is stuck, as a constructor split on a neutral.
* **Reflection happens during elaboration**, on closed data: the value is evaluated, turned into surface
  syntax whose object constants are resolved already (`SymRef`, never parsed), and elaborated like
  hand-written code, so families, implicit arguments, the core's checks and then the object level's
  (typing, stratification, termination) apply to reflected code. Data that is not closed (a postulate, a
  parameter of a meta function: reflection inside a function body that depends on its arguments) is
  E0918, as is data that is not object code (a variable without a name, a rule without heads, a dangling
  bound index). The opaque `⇑` staging remains for code generation under binders.
* **Where reflection applies.** An item `$e.` with `e : rule`, `item`, `seq rule` or `module` stands for
  the rules and queries `e` evaluates to; `$f a.` is read as `$(f a).` (in an item, a splice applied to
  arguments). Only at the top level of a file: in a module body it is E0907 (the rules would need the module's members, which are not object constants before the body is instantiated). In object
  code a value of type `formula` or `term` stands for the formula or term, with or without `$` (the
  coercion from `formula` to `prop` reflects); its variables are the item's variables of the same names
  (names are data, so this is by design, not capture), and they count as uses for W0002.
* **Positions and provenance.** Reified data carries the positions of its syntax (`Loc`, which evaluation,
  matching and unification look through), so the syntax generated from it has the positions of the
  quoted syntax it came from — a diagnostic in a rule built by `guard` points into `guard`'s right-hand
  side or at the rule the data came from. Generated items keep the span of the reflecting item (their
  place in the program) and carry a frame `in code reflected by `$e`` (`CoreItem.RuleItem.origin`,
  `QueryItem.origin`, passed on to `obj.Rule`/`obj.Query`), shown as a note.
* **Changes to the meta level that reflection needed.** (1) Strict positivity allows a family in an
  argument of another family that is strictly positive in that argument (nested inductives:
  `tapp : sym -> seq term -> term`). (2) An implicit binder of a constructor that is an argument of the
  constructor's result (`A` in `scons : A -> seq A -> seq A`) is forced, like a parameter, and does not
  count for predicativity; otherwise `seq term` would be one universe above `term` and the nested
  declarations inconsistent. So `vec : Type -> nat -> Type` is in `Type` now (was `Type₁`). (3) A
  constructor declaration must return a family of its own file: `x : formula.` in a program is a
  postulate, not a new constructor of the prelude's `formula`. (4) A declaration of the program shadows
  the prelude's name in the whole file, also before it: a forward reference to `term` waits for the
  program's `term` instead of resolving to the prelude's (this was latent before, for the prelude's
  `graph`, `pair`, …, and became visible with the common names above).
* **Goldens.** `tests/run/c1_guard` (§6.9's `guard`/`propagate`, run on a small type checker; it writes
  `typed_check` for `typed.check`, which C3 names), `c1_patterns` (`flip`, matching by symbol, literal
  patterns), `c1_aggregates` (higher-order holes), `c1_roundtrip`, `c1_splices`; negative:
  `e0917_quoted_syntax`, `e0917_no_prelude`, `e0918_reflection`, `c1_coverage`,
  `c1_reflected_diagnostics`, `c1_module_body`. `ReflectionSuite` checks both round trips (reflect ∘ reify on rules,
  reify ∘ reflect on data, up to the names of aggregate variables). Changed `.check` files:
  `neg/core_e0901_occurs` (meta numbers: the prelude elaborates more), `run/core_b2_clauses` and
  `run/core_b2_where` (`vec`, `pair` in `Type`, decision (2) above).
* **For C2.** `Reflection.reflectedItems(v, kind, span)` turns a closed `module`/`seq item` value into
  syntax, `elabSpliceItem` elaborates it with provenance; `reify(c, tree, kind)` quotes syntax (a
  directive's arguments). Missing: `Decl` (declarations as data), reflection inside module bodies,
  reflecting rule names. (C2 added `decl` and rule names, `inamed`; reflection in module bodies is
  still E0907, see "Directives".)

## Directives (redesign Phase C2)

Directives are meta functions (REDESIGN §7): `%d a₁ … aₙ.` resolves `d` like any name, elaborates the
application `d a₁ … aₙ`, and its type says what it changes (the *footprint*).

| file | contents |
|---|---|
| `syntax/DirectiveSyntax.scala` | `%d a₁ … aₙ.` (arguments are atoms), the prefix form, and the forms with a grammar of their own (`%infix`; `%mode` and `%fact` until C3) |
| `core/elab/Directives.scala` | resolution, the application, the footprint (`%mode` until C3; mode items since C3) |
| `core/elab/ModuleDirectives.scala` | module parts and the expansion of module-wide directives |
| `core/DeclAttributes.scala`, `core/handover/DeclData.scala` | `decl` values read back, and their attributes attached as object directives |
| `core/elab/DirectiveProblems.scala` | E0101 (unknown directive), E1000–E1003, E0701 |

### Declarations as data (prelude)

| type | constructors |
|---|---|
| `decl` | `dconst sym (seq attr)` (an object constant), `drule string (seq attr)` (a rule `@r`), `derror string` |
| `attr` | `ainput`, `aoutput`, `aopen`, `aderivations`, `aterminates measure (seq term)` |
| `measure` | `mvars (seq string)` (`X`, `(X, Y)`), `mlabels (seq string)` (`n`, `(n, m)`) |
| `item` (new constructors) | `inamed string rule` (a rule `@r`), `ierror string` |

`attach : attr -> decl -> decl` adds an attribute; the primitive directives are prelude functions:
`input D = attach ainput D.` (likewise `output`, `open`, `derivations`) and
`terminates : measure -> formula -> decl` (`%terminates X (r X _)`, `%terminates n r`).

### Decisions (C2)

* **Footprints by type.** The application `d a₁ … aₙ` (implicit arguments inserted) of type `decl` is
  *local*; `seq item`, `item`, `rule`, `seq rule` are *additive*; a function `module -> module` is
  *module-wide*; anything else is E1001. In the prefix form `%d a₁ … aₙ DECL`, `d a₁ … aₙ` must have type
  `decl -> decl` (E1002) and is applied to the declaration; the result must describe that declaration
  (E1003). REDESIGN §7.1 calls the standalone local form "`Decl -> Decl` ... rewrites the declaration it
  names"; here the name is the directive's last argument, quoted as a `decl` (`%input r.` is `input r`
  with `r : decl`), so both forms end in a `decl`.
* **What a declaration is as data.** A `decl` is an object constant (by symbol) or a rule name with its
  *attributes*; the declaration's type is not data (untyped reflection, Q5), so a local directive cannot
  change a type, only attach what the primitive directives attach. Where a `decl` is expected, an object
  constant (also a path `m.r`, a family, or in a module body a member) is quoted as `dconst ⟨r⟩ []` and a
  rule name `@r` as `drule "r" []`; where a `measure` is expected, the measure syntax of `%terminates` is
  quoted. Attributes accumulate: a local directive is given the declaration without the attributes of
  earlier directives (it cannot remove them), which keeps every local directive independent of the
  others, so they are elaborated item by item (see incrementality). C3 adds what `%demand` needs to
  *declare* constants (`r.check`).
* **Local directives are evaluated by the handover.** A local directive becomes a `CoreItem.DeclItem`
  (its `decl` term); the handover evaluates it — at the top level closed, in a module instance in the
  instance's environment — reads it back (`DeclAttributes`) and attaches the attributes as object
  directives (`DeclData`). So a directive in a module body may name the body's constants (the prelude's
  `bounded` has `%terminates N (hop _ _ N).`), and functions by clauses declared after the module body
  that uses them are available. Errors of the data (not a relation, E0701/E0406; another declaration,
  E1003; not closed, E0918; the directive's own `derror`, E1000) are reported there. An attribute of a
  family applies to each instance, as before.
* **Additive directives** are reflected in place like an item `$e.` (provenance "in expansion of
  `%symmetric friend`"); **module-wide** ones need the whole module: every object item records what it
  contributes (`ModulePart`: a rule or query as written, the data of a splice or an additive directive, a
  rewrite), and if there is a rewrite, the rules and queries elaborated item by item are replaced by the
  expansion: the rules, queries and splices of the whole file are the module's data, in source order
  (rules reified from their syntax, named rules as `inamed`); then the directives are applied in source
  order: an additive directive adds its items at its place, and a module-wide directive replaces the
  module with its result. So a module-wide directive sees every rule, query and splice of the file (also
  those after it) and the items of the additive and module-wide directives before it; only the items of
  additive directives after it are not seen (they are added to its result at their place). The result is reflected and elaborated; an item the directive passed on unchanged
  keeps its place and provenance, a new one is placed at the directive and notes it. Items with errors
  are not part of the module. Both are top level only: in a module body they are E0907 (the body's items
  would have to be reflected over its members, whose values exist only per instance).
* **Symbols by meta code.** In quoted syntax, a head that is meta code of a relation (or fact
  constructor) type — a clause's variable `R : ⇑(A -> A -> rel)`, a functor's parameter `g.edge`, a
  body's member — is a symbol (§8.5 writes `symmetric R = [ R Y X :- R X Y ].`). Symbols in reified data
  carry the position of their name, so errors about them point there.
* **User-defined errors** (DIAGNOSTICS.md, Q3): a directive rejects its input by returning `derror "…"`
  or an item `ierror "…"`; the message is reported as E1000 at the directive. Codes chosen by the user
  are not supported; the block E1000–E1099 holds E1000 and the machinery's codes E1001–E1003.
* **Resolution.** `%d` is E0101 ("unknown directive") if no `d` is in scope, with a similar name among
  the directives in scope (meta functions of a directive type, not the constructors of reflective data)
  as a suggestion. Without the prelude only `%infix` exists (and `%mode` before C3). A program's own `output` shadows
  the prelude's (then `%output` is E1001). A directive in a module body whose function is declared later
  in the file retries the definition after it, as other declarations do.
* **Removed.** The parser's, the core's and the handover's dispatch on directive names; `%name` (never
  used by any phase) and `%abbrev` (retired in B3, still parsed and ignored).
* **Parsing.** The prefix form is recognised by the declaration's `:` before the directive's end; the
  name before it (with its parameters) starts the declaration. A prefix directive and its declaration
  are two items; the directive is parsed from a slice that includes the declaration.
* **Tooling.** Hover over `%d` shows `d`'s declaration and footprint ("directive, local: it changes a
  declaration"); completion after `%` lists the directives in scope and those with their own syntax.
* **Incrementality.** Local and additive directives are object items of their own (a local directive's
  result does not depend on other items), so editing one elaborates that item only. With a module-wide
  directive the items are still elaborated one by one (for their diagnostics and index), but the
  program's rules are those of the expansion, which runs when the program is assembled
  (`ItemQueriesSuite`).
* **Goldens.** `run/c2_symmetric` (§8.5, with `⇑` and with `sym`), `run/c2_module_wide` (source order),
  `run/c2_primitive` (prefix form, composition, labels and variables, families, module bodies, rules);
  `neg/c2_directives`. Changed `.check` files: `neg/syntax_recovery` (`%frobnicate` is an elaboration
  error now, which a file with syntax errors does not reach; moved to `neg/c2_directives`),
  `neg/core_e0901_occurs` (meta numbers: the prelude elaborates differently), `lsp/navigation` (completion
  after `%` shows the directive's declaration, and a new hover over `%output`). `run/f_infix_abbrev` and
  `neg/typedefs` no longer use `%abbrev` (same output).

## Demand in the prelude (redesign Phase C3)

Demand is ordinary rules (REDESIGN D2, §3.6, §7.4), generated by the prelude's `%demand`, a module-wide
directive written in Hugin; the compiler has no demand transformation, no relation modes and no data
constructors.

| file | contents |
|---|---|
| `stdlib/prelude.hgn` | `bool`, the primitives, `modes`, `column`/`colof`, `irelation`, `demand` and its helpers (`d…`) |
| `core/Primitives.scala` | `same`, `labels`, `derive`, `derived`; derived constants and their declaration (also of families) |
| `core/elab/Declarations.scala` | `x : A = %builtin p.` for a primitive operation (E0103 if `A` is not its type) |
| `core/elab/Reflection.scala` | the item `irelation`; a pending derived constant is E0918 |
| `core/elab/Directives.scala`, `syntax/DirectiveSyntax.scala` | mode items `+e -t` as an argument (`ModeArgs`), elaborated to `modes` data |
| `core/elab/Quotes.scala` | named patterns `r { l = t, .. }` quoted as positional arguments (so module-wide directives see them) |
| `obj/transform/Disjunctions.scala` | disjunctions inside aggregates: the auxiliary relation's rules get their context (formerly its demand) |

### Declaring object constants from data

* **Derived constants.** `derive : sym -> string -> sym` names the constant `r.l` *derived* from `r`
  (`typed.check`): created on first use, memoised per constant and label like a family instance, so its
  name is stable (diagnostics, `--print-after`, LSP) and cannot capture a name of the program (it is a
  symbol, not a name looked up in scope). It is *pending* until an item `irelation (derive r "check") cols`
  declares it; a reference to a pending one is E0918. `derived : sym -> bool` tells derived constants.
* **Types are referred to, not reflected** (Q5): a column is `colof s k`, the column `k` of the constant
  `s` with its label and type; `irelation d cols` declares the relation over those columns. A column of a
  family makes the derived relation a family with the same parameters (`len.check : {A} -> list A -> rel`,
  instances `len.check[int]`). This is the minimal extension: `%demand` only ever needs the input columns of
  `r`; a reflective `ty` type of object types was not needed. Declaring other kinds of constants (types,
  constructors) from data is left open.
* **Why `same`.** Clauses split on symbols only by the constants they name; a directive over a parameter
  `r` must compare symbols (and variable names, for the binding analysis below): `same : A -> A -> bool`
  is decidable equality on atoms (literals and symbols, the values `CaseTree.SplitAtom` splits on), stuck
  on other values. `labels : sym -> seq string` gives the labels of a constant's columns (`""` without).
  The primitives are declared by the prelude (`same : A -> A -> bool = %builtin same.`) and checked against
  their types; their result constructors are taken from the declared types (`bool`, `seq`).

### Typed modes

`modes : seq string -> Type` is indexed by the labels of a relation's columns: `mnone : modes []`,
`minput, moutput : (l : string) -> modes Ls -> modes (l :: Ls)`, and
`demand : (r : sym) -> modes (labels r) -> module -> module`. The parser reads a run of mode items as one
argument (`ModeArgs`); the elaborator turns `+e -t +` into `minput "e" (moutput "t" (minput _ mnone))`
(by the prelude's constructors, which the program cannot shadow): an unlabelled item leaves its label to
unification. So `%demand typed +e +x -t.` is a type error (E0901: `"x"` against `"g"`), as is a wrong
number of items. `labels` reduces on the quoted relation during elaboration of the directive.

### The transformation (`demand r m`)

For the module `Is` (rules, named rules, queries, earlier generated items):

* `irelation r.check (inputs of r)` is added at the front.
* A rule of `r` (single head) becomes `r ā :- r.check ī, body` (its heads' wildcards at inputs are named,
  `_a`, `_ba`, …, so that the guard binds them), followed by its demand rules.
* Every call `r t̄` (positive, negated, in an aggregate, in a disjunction) of every rule and query gets a
  demand rule `r.check (inputs of t̄) :- prefix`: a *seed* outside `r`, a *propagation* rule inside `r`.
  The prefix is the formulas before the call (source order; the guard first in a rule of `r`), pruned:
  **demand rules are positive and do not wait for answers they do not need** — a negation is dropped, and
  a call of a demand-driven relation (one with a declared `.check`) or an aggregate is kept only if it
  binds a variable that the inputs (or the kept formulas) need and the other formulas do not bind. A
  smaller prefix only adds demand, never answers (magic sets with a weaker guard), and it yields the
  shape of REDESIGN §8.1/§8.2: `typed.check A G :- typed.check (app F A) G` without the call of `typed`
  on `F`, `fib.check B :- fib.check N, N > 1, A = N - 1, B = N - 2` without `fib A FA`. So the demand
  relation is in a component of its own, checked by descent (A), and `r` is checked by guarded induction
  (B) with the guard outside its component. Calls inside an aggregate use the formulas before the
  aggregate (its own formulas mention its bound variable).
* **Order independence.** Several `%demand` directives expand in source order, each seeing the output of
  the earlier ones. The demand rules generated from a rule follow it; a later `%demand` that guards a rule
  of its relation also guards the demand rules that follow it, and prunes the calls of its relation from
  every demand rule. So `%demand lookup …` before or after `%demand typed …` gives the same program.
* **Binding analysis in Hugin.** The pruning needs the variables a formula binds (an atom all its own, an
  equation its sides without arithmetic, an aggregate its result) and needs; it is written in the prelude
  over `seq string` with `same`.

The generated rules are ordinary rules: `--print-after stage` shows them (placed at the source rule they
come from when the directive is in another file, such as the prelude), their diagnostics note "in
expansion of `%demand …`", and they are typed, stratified and termination-checked like hand-written code.

### Decisions (C3)

* **`%mode` is removed**, not kept as an alias (Q10), under the standing no-baggage directive: there is no
  external user base. Re-adding it is one line in the prelude (`mode = demand.`, with `%mode` resolving
  to it as any directive).
* **All constructors are fact constructors** (D1): `%fact`, `ObjDecl` fact flags, `RelSym.isData`, data
  tables in the runtime, E0406 and E0504 are gone. A constructor term in a body is a pattern or an
  existence check; a list, context or other term becomes a fact when a head (a demand rule included)
  builds it. The type checker's contexts are `bind` facts (`--all-relations` lists them).
* **The prelude's `len`** measures the lists that are facts (`len (cons X L) M :- cons X L, len L N, …`,
  guarded induction on `l`). It cannot be demand-driven from the prelude: a module-wide directive
  rewrites its own module (REDESIGN §7.1), and the seeds belong to the call sites in other files (Q6). A
  program that measures lists it builds in bodies writes `%demand len +l -n.`: its seeds assert the lists
  (`len.check (cons "c" nil).`), and `len` measures them (`a06_termination_len`, `c2_primitive` give the
  old answers this way).
* **Relation modes and the moded checks** (E0502, E0503, mode arity and labels of E0701, signature
  `%mode` requirements of E0208 and their fix, `%mode` on formula functions, `ModeSpec`, `DirKind.ModeD`,
  `Moding.firstApplicable`, `CoreDirective`) are removed. Range restriction (E0501) is checked on the
  generated rules; a call whose inputs are not bound makes its seed not range-restricted, reported at the
  call with the note "in expansion of `%demand`".
* **Per-call copies are gone.** The cycles through negation they avoided do not arise with positive demand
  rules, except when a demand needs an aggregate over (or an answer of) the relation's callers; such a
  program uses a second relation (`tests/run/f_demand_negation_prefix.hgn`, `f_demand_disjunction.hgn`).
* **Disjunctions inside aggregates** (issue #1, B4/F1): the auxiliary relation `aux(ī, ō)` has no mode;
  each of its rules is the alternative after the context of the call (the formulas before the aggregate
  that do not mention a relation depending on the head, if they bind `ī`; otherwise all of them), which is
  what its demand rule was.
* **Termination.** `DemandDriven` (the moded case of Definition 10.3) is deleted: demand relations are
  checked by descent (A) and guarded relations by (B). **Known limitation**: a demand that needs an answer
  of the relation (Ackermann's `ack (M - 1) R1` after `ack M (N - 1) R1`) puts the demand relation and the
  relation into one component, which mixes the two directions and is rejected (E0603, with a note naming
  the mixed component; `tests/neg/t_termination_mixed_demand.hgn`), as are the other components mixing
  descent and guarded induction (Phase A). Formerly accepted with `%mode`; follow-up on issue #2.
* **Positions.** Reflected syntax uses the positions of the data it came from only within the file it is
  generated in: positions inside the prelude's quotes are not shown (a guarded rule points at the source
  rule, not at `dguarded` in the prelude), and a new item generated by a directive of another file is
  placed at the first position of its data in this file.
* **Named patterns** `r { l = t, .. }` are quoted as `r`'s positional arguments (a column not named is
  `_` with `..`), so programs using them can be rewritten by module-wide directives (a04).

* **Elaboration cost** (for issue #60). The prelude's demand code (about 250 lines of clauses) makes the
  prelude slower to elaborate: warm (in one JVM, after JIT) about 85 ms for the whole prelude against about
  13 ms without the demand section; cold (`hugin run` of a one-line program, `--stats`) `elaborate` about
  1.35 s against about 0.75 s before C3. Most of it was the termination check of meta functions
  (`core/elab/SizeChange`), which composed size-change graphs over the whole call graph after every
  function (about 500 ms warm); its closure is now restricted to the strongly connected components of the
  call graph (only they contain cycles), which does not change its verdicts. Further work is issue #60.

### Goldens (C3)

New: `run/f_demand_negation_prefix`, `run/f_demand_disjunction` (formerly the per-call-copy tests, same
answers with a second relation), `neg/t_termination_mixed_demand` (ack). Deleted (concept removed):
`neg/f_data_ctor_relation` (E0406), `neg/f_fact_ctor_moded_input` (E0504), `neg/formula_modes`,
`neg/t_termination_equation_ctor` (an equation no longer builds data), `fix/declare_mode`,
`fix/fact_constructor`. Every `%mode` became `%demand` and every `%fact` was dropped.

## Bound columns (redesign A2)

The rules are in `docs/REDESIGN.md` §5.2 (with the definitions of Kaminski et al. 2017 and Berent et al.
2022 they come from). Implementation: `obj/check/BoundColumns.scala` (E0605), `TypeConsistency.scala`
(E0606), `runtime/Store.scala` (one current tuple per key), `runtime/Divergence.scala` (value propagation
graph), `runtime/Infinity.scala` (`±∞`).

**Decisions.**

* *Best-value reading.* A body atom binds a bound column to the key's best value (the
  pseudo-interpretation of Kaminski et al.), not to every worse value of the limit-closed reading. For
  rules of the bound relation's own component the two readings agree by type-consistency (the optimum
  of a type-consistent rule is attained at the best values). Rules of *later* components read the final
  values as constants, as Kaminski et al.'s semi-grounding does for ordinary numeric atoms; this is what
  makes `report V D :- dist V D` useful and finite. Consequently type-consistency is checked only for
  *limit variables*: variables bound by bound atoms of the head's component.
* *Coefficients are literals.* Kaminski et al. allow `sᵢ·mᵢ` with `sᵢ` built from ordinary variables
  (constants after semi-grounding); since type-consistency then depends on the sign of `sᵢ` per
  instance, Hugin requires integer literals (`2 * D + C` is fine, `N * D` is E0606).
* *Binding equations* `X = t` over limit variables (with `X` bound nowhere else) are definitions and are
  substituted before the check; any other `=` / `<>` with a limit variable is E0606, and so is a constant
  in a recursive bound atom's bound column.
* *Termination.* The bound column of a bound head is not value invention (`Constructive.keyArgs`) and
  takes no part in size-change graphs or measures; the key columns are checked as before. *Soundness:* the
  check of §4 makes the set of keys finite (its arguments are about the facts' key columns; a body that
  holds for some best values satisfies the size-change arcs, which are derived from the body alone). With
  finitely many keys, a value improves only finitely often unless the value propagation graph has a
  positive cycle (Kaminski et al., termination lemma for stable programs), and every node on or after
  such a cycle becomes `∞` and never changes again; so evaluation terminates.
* *Divergence check at growing intervals.* Kaminski et al. check after every round. The engine checks
  after rounds 4, 8, 16, … of a component: building the graph costs a full pass over the component's
  rules. A positive cycle persists once present (stability: weights only grow), so it is found at the
  next check, and the number of checks is logarithmic in the number of rounds. Nodes *reachable* from a
  positive cycle are set to `∞` too (Bellman–Ford reports them together); this is sound, since an edge
  is a rule instance whose head term grows without bound with its premise (non-zero coefficient in the
  improving direction, and the instance stays applicable by stability).
* *`∞` as a value.* `∞` is a word of integer columns, printed `∞` / `-∞` (parenthesised when nested like
  negative numbers). Arithmetic and comparisons are extended (`runtime/Infinity.scala`); undefined
  combinations (`∞ - ∞`, `0 · ∞`, `∞ / ∞`) make the rule not fire, as overflow does. Type-consistent
  rules never meet them; a later component reading `∞` as a constant may. Input facts cannot contain `∞`
  (no syntax).
* *Not covered* (Q4): bound columns of constructors, `min`/`max` on
  floats.

**Testing.** `tests/run/rd_shortest_paths.hgn` (§8.3: a negative cycle gives `-∞`, a positive cycle
with `max` gives `∞`), `tests/run/b_bound_columns.hgn`, `tests/neg/b_bound_declarations.hgn`,
`tests/neg/b_type_inconsistent.hgn`. The naive evaluator implements the same semantics by Kaminski et
al.'s Algorithm 1 literally (every round, Floyd–Warshall, cycle nodes only), so the differential fuzz test
compares two different divergence procedures; `ProgramGen` emits bound columns over random weighted
graphs (about one in five such programs diverges).

## Parser (#53)

The review of the parser and the design are in `docs/PARSER.md`; this section records the decisions
taken while the designer was unavailable.

**Decisions.**

* *Rewrite the error handling, keep the grammar.* The recursive-descent grammar (precedence climbing,
  brace disambiguation, `where` layout) stays; the exception-based panic mode is replaced throughout by
  resilient LL parsing (matklad): no exceptions, error nodes, `expect` without consuming, recovery by
  construct, fuel. Parser.scala (553 lines) is split into six parts, each under 330 lines.
* *No lossless CST.* No consumer needs trivia (no formatter, no syntax-preserving refactorings); error
  nodes in the typed trees give the resilience; a CST can be added below them later.
* *Error nodes:* `Trees.ErrorTree(parts)` (missing or damaged syntax, with what parsed in it) and
  `Param.Malformed(tree)`. Items are kept with what parsed.
* *Repairs vs. damage.* Only recoveries that are certain about the intended text are repairs (the item
  is elaborated): an inserted `.` before the next item in an item that starts its line, `::` → `:`,
  adjacent `:=` → `=`, a parenthesised declaration head, a rule name on a declaration, an empty `where`.
  An inserted `)` `]` `}` is a guess: the suggestion is machine-applicable (so `hugin fix` repairs the
  common case), but the item is damaged and not elaborated (E0005's explanation shows why).
* *No cascading errors by construction.* The elaborator does not elaborate an item with a syntax error;
  it drops it silently and makes the names it might declare erroneous (also the head names of a broken
  rule: a declaration whose `:` is missing is a rule). Functions with a broken clause are declared but
  unelaborated; a module body with a broken member makes its whole item erroneous (its type would lack
  the member); erroneous names are silent in quotes, as directives and as clause declarations.
  Considered: partial elaboration with an error term of unknown type (rejected: the item is the
  elaborator's unit of recovery, and every later phase would need to know about holes).
* *One error per recovery region*: regions end at a new item, a body separator `,`/`;`, a list
  separator, or a closing delimiter reached by skipping.
* *Line heuristic.* A token in column 0 at the start of a line ends the current item in recovery. Two
  small changes to the accepted language follow from the same rule and are recorded in the reference:
  the operand of `$` and `⇑` and the arguments of a directive cannot start in column 0 (no program in the
  corpus wrote one there; a directive followed by a declaration in column 0 is still the prefix form).
* *`(e).l` is a projection*: `.` after `)` without space and before a lowercase letter is a selector
  (lexer); the reference says so. `.` after `]` or `}` is unchanged.
* *New code E0005* (unclosed delimiter), in the syntax block, with an explanation. `UnclosedModuleBody`
  (E0001) is replaced by it. The other syntax errors keep their codes; specific messages are cases or
  helps of `SyntaxError.Expected` (`SyntaxHelp`).
* *Messages:* expected sets are explicit per error site and rendered as phrases ("`.`, `,` or `:-`", "a
  type", "a label"), not as the set of tokens the parser happened to test; the start of a multi-line
  construct is labelled ("this rule starts here"; omitted for single-line items, where the snippet shows
  it). A missing period names the construct ("after the declaration"; a rule without body is a "fact").
* *Holes outside quotes* are not detected by the parser: `$x` is also an explicit splice, valid wherever
  the meta level allows one, and misplaced holes are E0917 (elaboration). Lowercase variables are
  detected where the grammar requires a variable (declaration parameters, `as`, `with`).
* *Fuzz property, k = 2.* `RecoveryFuzzSuite`: one deleted or inserted token, where it gives a syntax
  error, yields at most 2 syntax errors, no unresolved name outside the damaged line (except for a
  declaration whose name was destroyed), and leaves the following items parsed unchanged. k = 2 because
  one token can be two mistakes for the parser: a stray period inside an item (`x : int . -> rel.`)
  ends the item with a part missing, and the rest of the line is an item of its own that starts with
  junk. With k = 1 the property fails on exactly these; in 3600 mutants (12 seeds × 300) no case needed
  more than 2. Not covered (recorded in `docs/PARSER.md` §5):
  object-level errors about items that depend on a dropped item other than by name (a rule not
  range-restricted because its `%demand` was dropped), which predate #53 and apply to any dropped item.
* *Changed goldens:* `tests/neg/syntax_recovery.check` and `tests/neg/facts_errors.check` (wording of
  the missing-period message: "expected `.` after the declaration" / "after the fact" instead of
  "expected `.` after declaration" / "expected `.`, `,` or `:-`"). No other golden changed.

## Explicit quotes (#76)

Reflection has Scala-style quotes `'{ … }` (issue #76, approved). Before, object syntax was reified *by
expected type*: unmarked syntax where a reflective type was expected became data, and `(h :- b)` /
`(h :-)` was a rule. That made categories ambiguous (`(h :-)` existed only to force the rule category)
and collided with staging: `$[$(flip (edge a b))].` was elaborated as a staged list (E0901). Now
reflective data is always marked; staging stays inferred (Kovács) and unchanged.

| file | contents |
|---|---|
| `syntax/Lexer.scala` | `Tok.Quote`: a `'` at the start of a token directly before `{` (the `{` stays a token, so every depth count sees a brace); a prime elsewhere is a name character (`x'`) |
| `syntax/QuoteSyntax.scala` | `parseQuote`: entries `[@n] e [:- b]` and `?- b` separated by periods, closed with `close` (E0005 for an unclosed `'{`); `:-` in parentheses or a list is E0001 with the quote syntax as help (`SyntaxHelp.RuleOutsideQuote`) |
| `syntax/Trees.scala` | `Quote(entries: List[Item], terminated)`; `RuleQuote` is gone. A fact's single head is kept whole (`p X, q X` without `:-` is one formula) |
| `core/elab/Quotes.scala` | the analysis `Q`: `quotedContent` (a quote at a kind), `entry` (an entry as a rule or item), `quoted` (raw syntax) |
| `core/elab/QuoteTerms.scala` | quotes as terms (`reify`, `reifyQ`, whole-entry holes), implicit quotes of directive arguments, meta values in reified rules (#79), meta lists |
| `core/elab/ReflectionProblems.scala` | E0917 also for the shape of a quote's content and holes outside quotes; E0919 (new) for a quote without a reflective type |

**The grammar.**

```text
Quote ::= "'{" (Entry ("." Entry)* "."?)? "}"
Entry ::= RuleName? Expr (":-" Formula)? | "?-" Formula
Hole  ::= "$" Expr | "$" ".." Expr | "$" Expr "[" Expr ("," Expr)* "]"      (inside a quote only)
```

**Decisions.**

* **Categories by expected type, no prefixes.** `module`/`seq item` and `seq rule`: the entries, each an
  element (with its period, the last optional). `item`: one entry (a rule `irule`, a named rule `inamed`,
  a query `iquery`). `rule`: one entry without name or query; a fact is a rule without body. `formula`,
  `term`, `sym`, `decl`, `measure`: one entry without `:-`, name or period, read as before. Other list
  kinds (`seq formula`, `seq term`) are E0917 with a note to use a meta list of quotes. Lean-style
  category prefixes (`'rule{ … }`) are not added: every context that needs a quote has an expected type
  or can get one by an ascription, and a quote without one is E0919 with that help ("give the type:
  `('{ p X :- q X } : rule)`, or declare it"). The item `$e.` checks a quote (and a list that has no type
  of its own) against `module`, so `$'{ … }.` needs no ascription.
* **Holes only in quotes.** `$..xs` and `$f[t̄]` outside a quote are E0917 ("a hole outside a quote");
  `$x` outside a quote is the staging splice, everywhere. So meta lists lost `[a, $..xs]` (no program
  used it; `sappend` joins). The top-level item `$e.` is the splice applied to reflected data and stays.
  A hole's expression is meta code again, in which quotes may nest (`'{ p $(g '{ X }) }`); a quote
  directly inside quoted syntax is E0917.
* **Whole-entry holes.** A hole that is a whole entry (`'{ $r }`, `'{ a. $i. }`) has the entry's kind (a
  rule, an item). In an expression it may also be a `formula` (the fact) or, for an item, a `rule`: the
  hole's expression is inferred first, and its type chooses (so `$'{ $(flip '{ edge a b }). }.` works,
  the motivating example of #76). In a pattern it binds the whole entry. `'{ $..is. }` in a module is a
  sequence hole of items.
* **Directive arguments are quoted implicitly.** Requiring `%input '{ edge }.` or `%terminates '{ N }
  '{ hop _ _ N }.` would be noise without information: a directive is object syntax already, marked by
  its `%`. So an argument at a parameter of a reflective type (not a list) is read as the content of a
  quote (`QuoteTerms.implicitQuote`, by tree identity: `Directives.application` registers its argument
  trees); an explicit quote is accepted too. A meta value is passed in a hole, `%d $x.`. At `decl` and
  `sym` parameters only names (and holes) are quoted, so `%input 3.` stays a type mismatch (E0901). The
  prefix form `%d DECL` reifies the declaration as before. This is the one place where unmarked syntax is
  data; outside directives `'{ edge }` is written for a symbol (`$reversed '{ edge }.`, `fatom '{ p } []`).
* **Relations given by meta code** (a parameter `R : ⇑(A -> rel)`, a functor's `g.edge`) are symbols
  inside a quote, written as names (`symmetric R = '{ R Y X :- R X Y. }.`): they are object constants for
  the code, not meta values of a reflective type.
* **Unresolved names in quotes** are E0101 (with similar names) as in other code, not E0917: a name that is
  no symbol is elaborated once to report it. A member of a module whose declaration has a syntax error is
  silent (#53's rule for erroneous names).
* **Layout.** As in a module body, an entry of a quote does not start in column 0, so an unclosed `'{`
  ends before the next item (E0005) instead of swallowing the rest of the file (found by
  `RecoveryFuzzSuite`).
* **Printing.** `Printer.show` prints a quote as `'{ e₁. e₂ }` (the parser phase's output). Reflected data
  is printed by `--print-after elaborate` as constructor terms (`horn (scons …)`), as before; no printed
  output contained the old quote syntax, so no golden changed for printing.
* **Explanations.** E0917 is rewritten (no named patterns, no `(h :-)`, the categories of quotes, holes only
  in quotes); E0919 is new; E0918, E1001, E1003 use the new syntax. `(h :-)` and `[h :- b]` are E0001.

**#79 (fixed here).** A module-wide directive reifies the file's rules (`ModuleDirectives.reifyItem`), and
the reification met meta subterms: `k : int = 3. held : int -> rel. held k.` was E0917 with `%demand` in
the file, fine without. Now the rules are reified in a mode (`QuoteTerms.reifyingFile`) in which a term or
formula whose head is not an object constant (nor a hole) is elaborated as meta code and evaluated
(`metaValue`): a value of the expected reflective kind is used as it is (a `formula` meta constant in a
body), a base value becomes a literal (`tint 3`, also persisted values), object code becomes its syntax
(object constants applied to terms, arithmetic; implicit arguments dropped). Anything else is the old
E0917. An ascription in a term (`V = (nil : list int)`), which reflective data does not represent, is
left out when a rule of the file is reified (its type is checked again when the reflected rule is
elaborated); before, such a rule was E0917 with `%demand` in the file (found by `GeneratedFuzzSuite`
with a random seed). Goldens: `tests/run/c3_demand_meta_values` (a persisted `int` and an `⇑node`
constant in a file with `%demand`), `tests/run/c3_demand_ascription`; `docs/design/examples/typechecker.hgn` notes that the workaround it describes is no longer
needed.

**Changed `.check` files.** Only the syntax of programs changed; all answers are identical (every
`tests/run` golden passed unchanged after its program was rewritten). The negative goldens whose
snippets quote the rewritten lines changed in their source lines and columns only:
`neg/c1_coverage` (the clause of `loop`), `neg/c1_reflected_diagnostics` (`mk`, `typo`),
`neg/e0918_reflection` (the label now spans the entry `p 1 :- $opaque` of the quote instead of the
parenthesised rule), `neg/e0917_quoted_syntax` (same messages, new lines; E0917's general note reworded;
four new cases: a hole outside a quote, a rule where a formula is expected, two items where a rule is
expected, a quote at `seq formula`). New: `neg/e0919_quote_without_type`, `recovery/quotes` (the old rule
form in parentheses and in a list, an unclosed `'{`), `run/c3_demand_meta_values`,
`run/c3_demand_ascription`.

## Fuzz failures (#83)

Failures of `GeneratedFuzzSuite` and `RecoveryFuzzSuite` with non-default seeds (42, 7), each shrunk,
classified (program/generator, property, or compiler/engine) and fixed at the source.

**Recursive existence checks (engine).** `d0 N :- src N, _X = some N.` together with
`d1 (some N) :- d0 N.` puts `d0` and `some[int]` into one component: the existence check reads
`some[int]` (reference: object/facts, *Bodies never create facts*), and the head of `d1` builds facts of
`some[int]`, which the compiler derives in `some[int]`'s component (*Facts derived in other components*).
The lowering marked only atoms (`Scan`) as recursive reads; the `Lookup` of an existence check always
read the whole relation and did not count as a recursive atom. A rule whose only recursive read is an
existence check therefore had `recursiveAtoms = 0` and fired once, in the initial round, before the
rules of its component had derived anything; its facts were lost (the engine disagreed with the naive
evaluator). Fix (`ir/Lower.scala`, `runtime/Engine.scala`, `ir/IR.scala`): `Lookup` carries a recursive
index like `Scan`, assigned by the same counter in body order, and reads the version window of the round
(old before the delta read, delta at it, full after it). Correctness: a `Lookup` of `c t̄` is the atom
`c t̄` with every column checked (`(c t̄ as X)`), so semi-naive evaluation with one variant per recursive
read is exactly the standard differential of the rule; identities are in assertion order, so the window
test on the identity found is the same test a scan of the relation would make. Inside negations and
aggregates reads stay unversioned (stratification puts their relations in earlier components). Golden:
`tests/run/f_recursive_existence_check` (the shrunk program, and a chain that needs one round per step;
expected output derived by hand).

**Existence checks of built types (generator).** The other failures of seeds 7 and 42 in all three
properties (differential, metamorphic, demand) were one generator bug: `ProgramGen.equation` produced
`V = some X`, an existence check of `some[int]` (a *built* type, whose facts heads of later relations
construct). The checking relation then depends on `some[int]`, which depends on the bodies of every rule
that builds `some …` in its head; with a negation or aggregate over the checking relation in such a body
the program has a genuine cycle through negation, and E0601 is correct (reference: object/facts, the
note under *Facts derived in other components*). The W0002 warnings in the reports are incidental (the
generator often leaves singleton variables; warnings do not make a program rejected) and the demand
property failed only because both variants were rejected. Fix (`fuzz/ProgramGen.scala`): binding
equations check only constructors of read types (`cons X nil`) and `pt`, as the generator's invariant
for built types already said; recursive existence checks keep their coverage through a dedicated shape
(`existenceChain`: `xr N :- xs M N, _X = some M.`, `xm (some N) :- xr N.`), which nothing else reads, so
no negation joins its component. With the engine fix reverted, seed 7 finds the engine bug again through
this shape.

**A stray opener before an aggregate's braces (parser).** `RecoveryFuzzSuite` (seed 7) inserted `(` in
`C = count { X | f X ; g X N }, …`, which gave 3 syntax errors (> k = 2): `expected {` at `(`; then
`( { X` was parsed as a parenthesised brace expression whose recovery resynchronised, so the `|` was
reported by the end of the item, and the `(` was reported unclosed. The mutant is one mistake, and the
intended text is evident: an opening delimiter directly followed by `{` after an aggregate keyword is a
stray token. Fix (`syntax/ExprSyntax.scala`, `parseAggregate`): `(` or `[` followed by `{` there is
reported once (`expected {`), skipped, and the aggregate is parsed from the brace and marked damaged (an
inserted or skipped delimiter is a guess, so the rule is not elaborated, as for E0005). The property is
unchanged (k = 2). Golden: `tests/recovery/f_aggregate_stray_paren` (one error per rule, the items after
them elaborated). The seed no longer reproduces the mutant on its own, because the new goldens change the
corpus the mutants are drawn from; the shape was reproduced from three corpus files by hand.

**A stray `}` with its period (parser).** Verifying with more seeds, `RecoveryFuzzSuite` failed for seeds
19, 2024 and 77777 (on the merged quotes base) with the same tail: a quote that ended early (`'{ } R Y X
:- …. }.`, an entry `-> q …` after a period, an aggregate whose `{` was deleted, so its `}` closed the
quote) leaves the quote's own `}.` at the top level, reported as an unmatched `}` and then as an item
starting with `.`, which with the first error makes 3. The period right after a stray `}` is the end of the
item that `}` closed, not a mistake of its own. Fix (`syntax/ParserBase.scala`, `parseItems`): a stray `}`
directly followed by `.` on its line is skipped together with it. Golden:
`tests/recovery/f_stray_brace_period`.

**A use of a dropped declaration in a module body (elaborator).** Seed 23 deleted the `:` of `node : type.`
in `tests/run/c1_patterns`: `edge : node -> node -> rel.` is then dropped (its type uses the erroneous
`node`), and the module `m = { edge a c. }` (elaborated in the same round, before `dropPending` removes
the pending global `edge` from the scope) got E0101 "`edge` is used before its declaration", at the
dropped declaration: an unresolved name outside the damaged line, i.e. a cascade. The same happens
without any syntax error (`a : nodee.` with `nodee` undeclared). Fix (`core/elab/ObjectDecls.scala`,
`requireDeclared`): a pending global whose name is erroneous (its declaration was dropped for a reported
error) gives a silent error, as `Names.unresolved` does for erroneous names. Golden:
`tests/neg/f_dropped_declaration_in_module`. Not fixed (outside the property, which looks only at E0101
and syntax errors): in the same mutant, `$sappend (reverse '{ edge a b }) (reverse '{ m.edge b c }).`
reports E0901 at `sappend` when an argument fails silently; the splice-application fallback reports the
type of the bare splice instead of staying silent.

**A module body whose `{` was lost (parser).** Seed 19 (after the goldens above changed the corpus) deleted
the `{` of `select … = { sel : A -> rel. @s sel X :- r X, p X. }.` in `examples/formula_functions`: the
definition is damaged at `:`, `skipItem` stopped at the first period, and the indented members became
top-level items (`sel` unresolved in the rule, outside the damaged line; and `}` and `.` before the fix
above). Top-level items start in column 0 (the line heuristic of #53), so indented text after a period of
a damaged top-level item belongs to that item. Fix (`syntax/ParserBase.scala`, `skipItem`): at the top
level (no enclosing body or quote), a period followed by an indented line does not end the skip; the
skip ends before the next token in column 0 as before. Inside bodies and quotes, whose members are
indented, nothing changes. Golden: `tests/recovery/f_lost_module_brace` (2 errors, the items after the
body elaborated).

**Verification (#83).** With all fixes, at 100 tests per property: `GeneratedFuzzSuite` passes for seeds
1, 3, 5, 7, 11, 13, 19, 23, 42, 101, 314, 999, 2024, 31337, 77777; `RecoveryFuzzSuite` for the same 15
seeds; `MutationFuzzSuite` (10 tests per property) for seeds 1, 7, 42; and all fuzz suites with the
default seed. No property was weakened.

## Shared data (#80)

Shared (stage-polymorphic) data declarations, as approved in issue #80 after the design note
`docs/design/stage-polymorphism.md` (#52). `T ā : data.` with constructors declared as today declares
a type at both stages; stage inference converts meta values into object code by one rule, Lift.

| file | contents |
|---|---|
| `syntax/ItemSyntax.scala`, `syntax/Trees.scala` | `Kw.Data`: `data` is a keyword only as the whole type of a declaration (`T ā : data.`); elsewhere a name (`tests/run/c1_roundtrip` defines `data : module`) |
| `core/Core.scala` | `SharedLink` on both `GlobalEntry`s of a shared name: the side (stage), the counterpart, and on the meta family the ids of `T.lift`, `T.reify` |
| `core/elab/SharedData.scala` | the declaration (meta family, object family, `T.lift` declared), the constructors (meta and object constructor), the restrictions (E0920, E0921, E0923), `sharedAt` (a constant at a stage) |
| `core/elab/DerivedFunctions.scala` | `T.lift` and `T.reify` generated as surface clauses, with helpers for nested types |
| `core/elab/Liftings.scala` | the lifting judgement: the rule Lift (`liftCode`), its reflective counterpart (`reifyCode`), list syntax at the object stage, the first unshared type for E0902 |
| `core/elab/SharedProblems.scala` | E0920–E0923 |
| `core/elab/Coercions.scala` | `adjustStage`, `coeOpt`, `coeStaged`, `$e`: one call of `liftCode` instead of the cases for `⇑A` and base types |
| `core/elab/Bidirectional.scala`, `Names.scala`, `Records.scala`, `Quotes.scala`, `Declarations.scala`, `PiTypes.scala` | the stage of the position (`ElabState.stage`) and the resolution of shared names; `T.lift`/`T.reify` by name; members of imported files |
| `core/elab/QuoteTerms.scala` | holes of base and shared types reified; values of shared types in rules reified for module-wide directives (#79) |

**Generated items and their typing.** For `T a₁ … aₙ : data.` with constructors `cᵢ : σ̄ᵢ -> T ā`:

```text
T       : Type -> … -> Type                       meta inductive family (GlobalKind.Inductive)
cᵢ      : {ā : Type} -> σ̄ᵢ -> T ā                  meta constructors
T       : ⇑type -> … -> ⇑type                     object family (GlobalKind.Family), or an object type (n = 0)
cᵢ      : {ā : ⇑type} -> ⇑(σ̄ᵢ -> T ā)              object (fact) constructors
T.lift  : (A₁ -> ⇑B₁) -> … -> T Ā -> ⇑(T B̄)        T.lift F̄ (cᵢ X̄) = cᵢ (L[σ] X)…
T.reify : (A₁ -> term) -> … -> T Ā -> term        T.reify Ḡ (cᵢ X̄) = '{ cᵢ $(R[σ] X)… }
```

The meta and the object constants are elaborated from the same declaration, at the meta stage (unknown
types as meta types) and at the object stage (unknown types as object types); the object side is
declared without a name in scope (`declareHidden`) and found through the link. Both are made by the
existing declaration code, so everything downstream (coverage, families and their instances, the
object typer, the handover) is unchanged. `T.lift` and `T.reify` are declared as functions with a type
built as syntax and defined by clauses built as syntax, elaborated by `elabFunction`; coverage and
size-change termination are checked as for hand-written functions (none was disabled). In the clauses
an argument of a parameter's type is converted by its element function, one of a closed type by stage
inference itself (`X` in object code is lifted, `$X` in a quote reified), one of a type of the file by a
direct call. `T.reify` exists where `term` is in scope; the prelude declares `list` before `term`, so
there it is declared after the file's declarations (before the clauses of functions, so programs can
use it like any function).

**Nested types (decision).** In `node : list (tree A) -> tree A` the naive clause is
`node $(list.lift (tree.lift F1) X1)`, a call of `tree.lift` that size-change termination cannot see
(it is an argument, not a call). Instead of skipping the check for derived functions, a nested
occurrence (a shared family applied to types that mention the file's shared families) gets a helper
`tree.lift.1 : (A1 -> ⇑B1) -> list (tree A1) -> ⇑(list (tree B1))`, the fold of `list` specialised at
`tree A1`, with direct calls of `tree.lift` and of itself, as the prelude writes `openTs` next to
`openT`. Helpers are memoised per owner and type. The generator works on the constructors' elaborated
types (a small `Ty` of parameters, base types and applications of shared families), not on their
syntax, so it covers constructors of other files (`list`'s for a nested `list (tree A)`), and refers to
constants by id (`SymRef`, which now resolves by the stage of its position like a name; constructor
patterns accept a `SymRef`).

**Names and stages (decision).** A shared name in scope is its meta constant; `Names.resolve` takes the
counterpart when the position is an object position. `check` and `inferS` set the stage of the
position (`ElabState.stage`, meta outside them; `$e` elaborates `e` at the meta stage). In a declared
type whose stage is inferred, the position has the stage of the declared constant's result (probed by
inferring the codomain): `wrap : list int -> box.` is an object constructor with an object list column,
`size : list int -> int.` a meta function (the object alternative of `declType` fails for a result of a
base type, as before). Parameters of formula functions are object code, so a shared type there is the
object type. A member of an imported file (`c.color`) is its meta constant, and the object constant at
an object position (`tests/run/s_shared_import`). Inside quotes names resolve to object constants
(`objectConstant`, also through `SymRef` and paths). The list syntax `[ē]`, `e :: es` is the prelude's
(reflective) `list` at the stage of the position: meta lists as before, object lists in object code
and in quotes (desugared to `cons`/`nil` by reference).

**The rule Lift as implemented.** `liftCode(c, t, τ)`: `⇑A` gives `$t` (rule Code), a meta base type
`Tm.Persist(t)` (rule Base), a shared family applied to `τ̄` gives `$(T.lift ℓ̄ t)` with the element
liftings `ℓ̄` built recursively as meta functions (`[x] x` for code, `[x] ⟨persist x⟩` for base types,
partial applications of `U.lift` for shared types), the implicit arguments of `T.lift` solved by
unification with the types of `ℓ̄` and `τ`; otherwise no lifting. The base-type persistence of
`adjustStage`, `coeOpt` (`Base S1` to `Base S0`), `coeStaged` (`isMetaPrim`) and the explicit splice are
replaced by this one function: persistence is the instance Base, the splice the instance Code (no
separate rule remains). A meta value of unknown type used as object code is still taken to be object
code (`unify` with `⇑?m`), as before. `reifyCode` is the counterpart for holes: `tint`/`tfloat`/`tstr`,
`T.reify ḡ`, no rule for `⇑A`; a hole `$e` at a term infers `e` first and, if its type is not `term`
but has a reification, applies it (otherwise checks against `term` as before). In a file with a
module-wide directive, a value of a shared type in a rule is reified as its object constructors
(`termData`), as #79 does for base values.

**Restrictions.** E0920: a constructor argument whose type is not a parameter, a base type or a shared
type applied to such types (checked on the elaborated meta type, so a variable that is not a parameter
or a dependent argument is caught too). E0921: a result other than `T ā` at distinct implicit
parameters, `T` at other arguments in an argument (polymorphic recursion), or a typed parameter in the
declaration. E0922: an edge or refinement into a shared type (or an instance of a shared family).
E0923: `data` in a module body or `where` block (reported where `inferKeyword` meets it), and a
declaration returning a shared type of another file (`single : A -> list A.` in a program; before, a
program could add constructors to the prelude's `list`; no test or example did). A declaration with
clauses or a definition returning a shared type is a function, as before.

**Prelude.** `list A : data.` (constructors as before, unlabelled, so column labels and outputs are
unchanged) and `option A : data.`; `append` (meta) replaces `sappend`; `seq`, `snil`, `scons` are
removed, and the reflective types, `labels`, `modes` and the `%demand` code use `list` (mostly through
`[]` and `::`). `pair` stays an object struct, `bool` meta only. `ReflectiveGlobals` has `list`, `nil`,
`cons`, `append`; `DeclAttributes` and `Reflection` match `nil`/`cons`. The line of `len`'s recursive
rule (19) is kept, because termination explanations print it.

**Not done (decisions of the issue).** No `lower`, no typed holes in quoted patterns, no shared records,
no stage-polymorphic functions, no shared aliases (`name : data = string.` of the design's §5.1; the
issue lists only `T ā : data.`). The derived functions of an imported file's shared type are inserted by
stage inference but cannot be named (`c.color.lift` is not a path). In the REPL a declaration whose
clauses come in a later input is classified without them, for shared result types as for meta
families (pre-existing).

**Observation.** `ObjectDecls.predeclare` compares `d.tpe == Keyword(Kw.Type)`, which compares a tree with
a partially applied constructor (`Keyword` has a second parameter list) and is always false, so
constructors are never predeclared; the dependency-order retry covers them. Not changed here (the shared
declaration test uses a pattern match).

**Changed `.check` files.** No answer of a `tests/run` golden changed. The design examples were not
goldens before; their outputs are identical to the pre-#80 versions (checked with a build of the base).

| file | why |
|---|---|
| `neg/c1_coverage` | the program says `list rule` for `seq rule`; the missing case prints `nil` for `snil`, the clause `cons`/`nil` |
| `neg/c2_directives` | E1001/E1002's note says `list item` (`list rule`) |
| `neg/core_e0901_occurs` | the numbers of the unknowns (`?167` for `?151`): the prelude creates more metas (the derived functions) |
| `neg/core_e0902_meta_as_object` | E0902's note names shared data types among what can be used as object code, and a new note says `nat` has no lifting |
| `neg/e0917_quoted_syntax` | columns after `list` for `seq` in the program; E0917's note says `list rule` |
| `recovery/f_stray_brace_period`, `recovery/quotes` | the program after `elaborate` prints `list item`, `cons`/`nil` for `seq item`, `scons`/`snil` |

New goldens: `neg/e0920_not_shareable`, `neg/e0921_not_uniform`, `neg/e0922_edge_into_shared`,
`neg/e0923_shared_out_of_place`, `run/s_shared_data` (nested, mutual, floats and strings, object list
syntax, explicit `T.lift`/`T.reify`, `list (⇑int)`, reified holes), `run/s_shared_import`, and the
three design examples (`GoldenTests` runs `docs/design/examples/*.hgn` like `tests/run`).
`SharedDataSuite` checks `reflect (T.reify v) ≡ T.lift v` differentially (ScalaCheck, random values of
`tree (option int)`, `list (list string)`, `option (tree float)`, `stmt`, `list (option int)`: the staged
programs with `held v.` and `$'{ held $v. }.` are equal).

## LSP for the meta level (#54)

The language server learned the meta level: hover with elaborated types and stages, navigation through
patterns, lambdas, `where` and quotes, semantic tokens by level, inlay hints for what stage inference
inserted, the expansion of directives and functor applications, typed holes with code actions, and
type-directed, quote-aware completion. `docs/LSP.md` has the audit, the features, the protocol and the
test of each feature. Decisions (the designer was not available; all are open to revision):

- **Where the information comes from.** The elaborator records, in a `MetaIndex` of the semantic index,
  the type and stage of every expression checked or inferred at a stage (`check`/`inferS`), the
  conversions `coe`/`adjust` insert, implicit insertions, universe levels, goals, split candidates,
  missing clauses and directive applications (`core/elab/MetaTooling.scala`). Types must be shown with
  the solutions of unknowns found later, and attempts that are undone (a declaration tried at the other
  stage, `undoOnFailure`) must leave nothing: records go to a *tooling log* in the core, truncated with
  the metas by the checkpoints, and flushed at the end of each item once it is known whether it
  succeeded. A successful item's records are kept as closures evaluated when a language server asks
  (its core does not change afterwards), so compilation pays only for the closures; a failed item's are
  evaluated at once, before its metas are undone (they then show `?n` for unknowns).
- **`Ide` stays as it is.** `hugin query` and the REPL's `:type` print `Ide`'s answers; the new
  information is in `MetaIde`/`Expansion` and only the language server shows it, so no CLI output
  changed (except that `hugin query` now also finds pattern variables, lambda parameters, `where`
  bindings, constructors in patterns and clause names, which are new symbols and references).
- **Hover shows the innermost recorded expression** with its text: an expression checked or inferred at a
  stage, or the head of an application (`ident` in `ident 3` shows `int -> int`, elaborated `ident
  {int}`). Inside a directive application the application's type and footprint are shown instead of the
  quoted data its arguments become.
- **Typed holes** (`?`, `?name`; E0924) are a new expression form: `?` not followed by `-` (so `?-`
  stays the query token) with the name characters directly after it. A hole is checked like any
  expression, as an unknown that may stay unsolved, so the item elaborates and every hole is found; each
  is an error once the item's other unknowns are solved (reported only if the item otherwise elaborates:
  the error of a failed item is the one reported), so compilation stops before staging. Staging does not
  report code stuck on a hole again (E0909). The name only identifies the hole in messages. Holes in
  quotes are not quoted syntax (they are reported as such).
- **Coverage collects every missing case** (up to 20) for the code action, but E0911 is unchanged: it
  reports the first, and an error found after a missing case is replaced by that first missing case, as
  before, since the checker used to stop there.
- **Split** offers the constructors whose indices unify with the variable's type (`head : vec A (suc N)
  -> A` splits into `vcons` only) and replaces every occurrence of the variable's token in the clause
  text (its binding and its uses); a lambda parameter of the same name in the right-hand side would be
  replaced as well. New variables are named after the constructor's binders, or after the variable
  (`N1`, `N2`). Literal and quoted patterns are not split.
- **Clause skeletons** are offered for meta postulates with explicit arguments: a declaration whose
  result is an inductive type declares a constructor, so a function returning one only gets clauses once
  it has a clause.
- **Type-directed completion matches heads**, not types: a candidate fits if the head of its result type
  (a family's name, a base type, `type`, `prop`, …, through `⇑`) is the expected type's. The expected
  type is recorded when the name being typed fails to elaborate (with the variables in scope), which is
  the usual state while typing.
- **Expansion** uses the object program as staging produced it (`CompilationUnit.staged`, before the
  object-level phases rewrite it): the items whose expansion chain contains the innermost directive or
  functor application around the position, otherwise the staged instances of the item there. Code
  lenses are on every application that produced items.
- **Semantic tokens** keep the first eight legend types in their order and add `decorator`, `keyword`,
  `operator`, `method`, `class`, `label`, with the custom modifiers `meta` and `object` (declared by the
  VS Code extension); meta and object names are told apart by the modifiers, so themes without them
  still colour by type.
- **Inlay hints** default to staging and implicit arguments on, levels off; implicit arguments of object
  families (`cons {⟨int⟩}` in hover, `{int}` hints) show the object type quoted, as elaborated.

Deferred:

- Features inside items with syntax errors (dropped by the parser, #53).
- Hover on module members inside a module body (their binders have no site) and on quoted object syntax
  beyond its variables and constants.
- Refining a hole with a function whose result fits (holes are refined with the constructors of an
  inductive goal, not filtered by index unification), splitting literals and quoted patterns, full
  unification for completion.
- Expansion of local directives (their `decl` attributes) and of a family's instances from its
  declaration; navigation from the expansion document back to the meta code is by the origin comments
  it shows, not by links.

## Long lists and the bench harness (#88)

`sbt "Test/runMain hugin.bench.Bench warm"` overflowed the stack in `meta_scaled` (docs/PERFORMANCE.md,
"After #80–#87", has the stack trace's analysis and the numbers). Decisions:

* **Root cause, not a larger stack.** The harness runs on the JVM's default 1 MiB stack, the launcher on
  64 MiB; the overflow was JVM stack spent per element of a list: the module-wide directive `mirror`
  recursing over ~190 items at ~40 frames per item. The #60 final build overflows the same way today
  (JIT-dependent), so this is not a regression of #80–#87; the issue's suspects (explicit quotes, shared
  `list` with derived folds) only contributed the deep case tree of a quoted pattern.
* **What is now constant-stack per element**: case-tree matching (`Matching.runTree` is a loop, so a
  meta function's recursion costs the same frames per level whatever its case tree), the memo keys
  (`MemoKeys`: recursion up to depth 200, then an explicit stack — an explicit stack on every call cost
  +28 % on meta_scaled), evaluation of argument chains (`cons x1 (cons x2 …)`, in the recursion's order:
  functions and arguments left to right, each application after its argument), and the elements of a
  list value (`Reflection.elements`).
* **What stays proportional to the length** (recorded, not changed): a meta function's own recursion over
  a list, including the derived `T.lift`/`T.reify` folds (the evaluator is a recursive NbE evaluator;
  making it stackless — CPS or a trampoline through `eval`/`app`/`reduceFunction`/`quote` — is a redesign);
  read-back (`quote`) of a long list outside the memo keys; and parsing/elaborating a source list literal
  of thousands of elements (`Slices.congruent`, the elaborator). Measured on the 1 MiB stack, cold: a
  literal list lifted to object code (`p [1, …, n]`) overflows from ~150 elements, a recursive directive
  from ~590 items (was ~190); on the launcher's stack all of them pass at 10 000 elements.
* **Tests** (`core/LongListsSuite`) run on a thread with an explicit 1 MiB stack (the harness's
  situation), so they do not depend on the test JVM's thread configuration: a module-wide directive over
  5 000 items, `mirror` over 400 items, memo keys and evaluation of a 100 000-element list. All three
  overflow before the fix.
* **Performance regressions found** while re-recording the numbers (each re-measured against a build of
  the #60 final commit on the same machine): `shortest_grid` +25 % from `Operators.declared`
  (`sliding(4)` over the tokens of a 14 000-line facts file; now a loop), fixed; uncached prelude
  elaboration +40 % from new work (tooling records of #54, derived functions of #85, the resilient parser
  of #53), recorded — making `Clauses.recordSplits` lazy changes the state it reads.

## Predeclared constructors (#86)

`ObjectDecls.predeclare` compared `d.tpe == Keyword(Kw.Type)`, but `Keyword` has a second parameter list
(its span), so the right side was a function and the test always false: no open type was recognised and
no constructor was predeclared. Forward references to a constructor already worked without it
(`elabInDependencyOrder` retries an item after the declaration it refers to), but a **cycle through a
constructor** did not: `neg : (e : small) -> expr.  lit : (v : int) -> expr.  small : type = lit | neg.`
reported E0101 for `small` and `neg` (in either order of the declarations). Decision: fix the
predeclaration rather than remove it (a pattern `Decl(n, Nil, Keyword(Kw.Type), None, None)`: a plain
open type, no parameters, refinement or definition), as the design note of B3 ("Cycles between object
declarations") describes. `HandoverSuite` covers a forward reference, the cycle in both orders and facts
of the cycle's constructors.

## Typed object code (#56)

Object code is typed in the meta level where it is written, and reflection has a typed layer. The design
is `docs/design/typed-object-code.md` (a survey of Lean 4, Qq, Scala 3, Kovács's staged elaborator and
typed Template Haskell from their sources), approved by the designer as written; it covers the triage
items C1 and C2 of `docs/history/TRIAGE.md`. Batch A (object typing in the core) is PR #93; batch B (typed
reflection) follows it.

| file | contents |
|---|---|
| `core/objtype/OTy.scala`, `ObjEnv.scala` | object types by their heads (globals, and context variables during elaboration), the constants and edges in scope, values to types |
| `core/objtype/ObjTypes.scala` | subtyping, members, meets, joins (ported from `obj/typing/TypeOps`); abstract types |
| `core/objtype/Typed.scala`, `ObjWalk.scala` | object code as the checker reads it, from core terms (elaborated or staged) |
| `core/objtype/ObjCheck.scala`, `ObjRecords.scala`, `ObjProblems.scala` | the checker (ported from `RuleTyper`): meets of variables, equations, subsumption, operands, projections; E0303–E0305, E0401–E0405 |
| `core/elab/ObjectTyping.scala` | the end of each scope: rules, queries, formula-function clauses, object code in meta definitions, clauses and meta-function arguments; `⇑` covariance |
| `core/handover/StagedTyping.scala` | the check of staged items, and the variable types of every item for the object phases |
| `core/elab/TypedQuotes.scala` | `quoted A`, its coercions, the types of holes, the check of quotes |

Decisions:

* **One checker, read from core terms.** The design note has the elaborator feed constraints while it
  elaborates; the implementation reads the elaborated core terms at the end of each scope instead, with
  the context's types and the constants' types, and the types of spliced meta code read off the types
  of variables and globals applied to arguments. Elaboration still unifies object types where it can and
  keeps a term whose types do not unify (that solves implicit arguments); object typing decides. The
  same checker reads staged items after the handover (Lean's kernel boundary): it reports only for items
  that involve meta code (a splice, a persisted value, `fresh`, a module instance, a generic rule,
  reflected code), and gives every item the variable types that `records` and `disjunction` use. Variable
  types found by meets solve the unknown types of variables, which determines implicit type arguments
  (the case under "Open issues (after Phase B)").
* **Functor bodies (C1)** are typed once: the types a parameter gives (`g.node`) are abstract, a subtype
  only of themselves (and of what edges say), so `out X :- g.edge X X.` with `out : (x : expr) -> rel` is
  E0402 at the body. Operand checks over an abstract type (comparisons, arithmetic, a literal in its
  column, projections) and meets with it are left to the instances. A probe over every program of
  `tests/`, `examples/` and the design examples found no program that the rule rejects.
* **`⇑` is covariant (C2)**: `⇑τ` is accepted for `⇑σ` if `τ ≤ σ`, also where a quote cancels a splice
  (`w X = up X` with `X : ⇑var`, `up : expr -> prop`). Spliced code at an object position is coerced
  like other object data, so a misplaced one is E0402 (was E0901).
* **E0404** is reported by the declarations: an edge's member at the edge, refinements and union columns
  after the file's declarations. The edges of a module body are elaborated before its rules.
* **`quoted A`** is a prelude inductive type former with the unchecked constructor `qterm` (the escape
  hatch, Qq's `unsafeMk`) and `raw`; it is not a definition, so that conversion never unfolds it into
  `term` (#66). It is accepted as a `term`, covariantly in `A`, and stands for its term in object code.
* **Quotes are checked from their analysis.** The design note has quote content elaborated as object
  code and reified from the core term; the implementation checks the existing analysis of a quote (`Q`,
  the one reading shared by expressions and patterns) with the same checker and reifies from it as
  before. Elaborating holes of type `term` as object code would need placeholders instead of reflection
  (which fails on open data, E0918), and named patterns and dropped implicit arguments would need cases
  of their own; with one reading the risk the note names (two readings that disagree) does not arise.
  Holes are checked at their types: `quoted A` at `A`, `term` at an unknown type, a base or shared value
  at the type it lifts to. The rules of a file reified for a module-wide directive are not checked again.
* **Typed holes** of quoted patterns: a hole at a column of a resolved constant with a base type or a
  constant's type binds `X : quoted τ`, through a variable for the data and `X = (qterm X#data : quoted τ)`
  in the clause's `where` block (as higher-order holes do); case trees and coverage are unchanged, and
  the type is not tested when matching (reflection checks the data again).
* **Hygiene of generated names.** `%demand` names the wildcards of guarded heads `_a#0`, `_ba#0`, …:
  source syntax cannot write `#`, so a program's `_a` is not captured (it was: `run/ot_demand_hygiene`
  answered `no.`). Names still display as `_a`.
* **Cost.** Measured in process (gen_large, 10 warm runs): the checks during elaboration 3–4 % of the
  run, the check of staged items 1.5–3 %; the warm bench set is within noise of the base (interleaved runs
  against a build of 50a893c). The columns of global constants are cached with the core.

Goldens: `neg/ot_generators`, `neg/ot_functor_once`, `neg/ot_typed_quotes`, `run/ot_lift_upcast`,
`run/ot_meet_implicit`, `run/ot_typed_patterns` (with a round trip), `run/ot_quoted_terms`,
`run/ot_demand_hygiene`. Changed: `neg/c1_coverage` (`raw` in a printed clause),
`neg/c1_reflected_diagnostics` (an ill-typed quote is reported at the quote), `neg/core_e0901_occurs`
(numbers of unknowns). Two unit tests of `HandoverSuite` and `ModulesSuite` were ill-typed (they stopped
before the object typer ran) and were made well-typed.

### Fixes after the reference audit (#98)

The audit of the reference (#97) found seven places where the implementation fell short of the design
(entries 16–22 of `reference/DISCREPANCIES.md`, removed with the fixes): object code in record fields,
`where` definitions, definitions with an inferred type (an atom of type `rel` is a formula) and formulas
passed to meta functions inside object code is typed at the definition; a rule whose head is not a family
instance reports an undetermined type argument as E0206 (it was made generic, then E0909 at staging); an
error of the check of staged items in code generated elsewhere has the note "in the code staged for this
rule"; a directive argument at `quoted A` is quoted implicitly; `$f a.` is a splice item when `f` returns
reflected items, whatever the argument (so its error is the argument's); `data` in a `where` block is
E0923; an equation that is a conjunct of the body meets the type of a variable with columns (not in an
alternative of a disjunction). The generated fuzz programs no longer equate a variable with constants of
two constructors, which is now a rule that never fires (E0401).

## Frozen metas (#66, Batch 1)

Design: `docs/design/elaborator-glued.md` (branch `design/elab-66`), section 4.1. Each declaration,
clause group, formula function and object item is a *block* (`Core.inBlock`, called by `Items`). While a
block is elaborated, the metas that existed when it started are frozen: `Core.solveMeta` refuses them
(`UnifyFailure.Frozen`), `unify` treats them as rigid (against an active meta it solves the active one;
the same frozen meta on both sides compares the spines), and `pruneFlex` does not prune them. A block
inside a block is part of it. Outside blocks nothing is frozen, because staging solves the unknowns of a
generic item for each instance (`Core.tentatively`).

Before, an unknown that may stay unsolved (a hole) could be solved by a later item: `t : Type = ?t.`
followed by `x : t = 5.` solved `?t := int`, and `y : t = "s".` then reported "expected `int`". The
reference already said a hole is constrained by its item only. A frozen hole now makes the later item
fail silently (`ElabErrors.mismatch`): its E0924 is the error. A spike that logged every cross-block
solution found none in the golden, core, reference, LSP and incrementality suites, so no other program
changes. Object typing (#56) solves its store inside the block, before the block ends, so freezing
follows it.

Unknowns print numbered from the start of their block (`Printing.showMeta`): `?3` instead of `?167`, so
messages do not depend on the number of metas in the prelude. `Core.fork` keeps its copy-on-write of meta
entries: an item's fork can no longer solve a base meta, but `allowUnsolved` still writes entries, and a
parent core may go on elaborating after a fork.

## Typed reflection beyond terms (#96)

The design is `docs/design/typed-formulas.md` (Qq, Scala 3, MetaOCaml, generic-syntax, Kovács, λProlog,
Twelf and Abella read from source), approved by the designer as written: no context index and no typed
formula type; the context of a generated piece is the meta context of its `quoted A` values. It lands in
three batches.

* **Batch 1, repeated holes.** `TypedQuotes.QuoteReader` reads a hole `$X` (a variable of type `quoted A`
  with a known `A`) that occurs more than once in the body of a quoted rule, query or formula as one
  object variable `$X`, with `A` as a further bound (`OFormula.Expect`), so the checker's meets apply
  (E0401 at the generator). A hole used once keeps the per-position check of #56 (so no diagnostic of an
  existing program changes), and a hole in a head keeps `A ≤ σ`, since the data may be a constructor term.
  The identity of a hole is the name of the variable it refers to in the quote's context, which is fixed
  for the quote. Holes of type `term` and of base or shared types are not merged: their data need not be
  a variable of one type. Golden `neg/tf_repeated_holes`; no check file changed.
* **Batch 2, typed atoms.** `qatom : quoted A -> formula = %builtin qatom.` is a primitive
  (`PrimOp.QAtom`, with `fatom`, `tapp` and `qterm` found from its declared type): it reduces the data
  `qterm (tapp s ts)` to `fatom s ts` (the same spine, with the positions of the quoted syntax kept) and
  is stuck otherwise. It is not a definition, so glued evaluation (#66) never unfolds it, and `quoted`
  stays a postulated type former. `TypedQuotes.coeQuoted` inserts it where a `formula` is expected and
  the index is a type of facts (`ObjTypes.isRelLike`, which also admits an index the core does not know,
  such as an unsolved one: reflection checks the data then); otherwise E0901 with a note. A whole entry
  `'{ $a }` of a typed atom is its fact (`QuoteTerms.entryHole`). Reflection reports a `qatom` stuck on
  closed data as E0918 ("the term `tvar "E"` of a `quoted` atom is not an atom"). The quote reader needs
  no change: a typed atom's columns were checked where it was built, at constructing positions.
  Deviation from the design note: open types are types of facts (their values are facts of their
  members, and every constructor is a relation), so `quoted node` for an open type `node` is an atom;
  the note's example of a rejected index is a base type. The section "Typed terms" of the reference keeps
  its name (its anchor is linked from other chapters) and gains a subsection "Typed atoms".
  Goldens `run/tf_typed_atoms` (atoms as facts, items, heads, bodies, under `not`, and taken apart by a
  quoted pattern), `neg/tf_typed_atoms`. Changed: `neg/core_e0901_occurs` (numbers of unknowns, which
  count the prelude's declarations).
  The new golden shifted the mutants that `RecoveryFuzzSuite` draws from its fixed seed onto a weakness
  of the parser that it had not met: `?-` at the end of a line took the declaration in column 0 of the
  next line as its formula, so the declaration was lost (E0101 for its uses). The formula of a query and
  the body of a rule now do not start in column 0, like an argument and the operand of `⇑`
  (`ItemSyntax`); no program of `tests/`, `examples/`, `docs/`, `bench/`, the reference or the prelude
  starts one there. Reference: lexical-structure ("Items"); `docs/PARSER.md` 4.2; golden
  `recovery/r_col0_formula`.
* **Batch 3, typed variables and W0007.** `qvar N = qterm (tvar (N ^ "#v"))` is a prelude definition,
  so its data is ordinary and the same hint gives the same variable. Its type argument is stated by the
  program (a declared type, a parameter type): `$(qvar "x")` written directly in a hole leaves it
  undetermined (E0903), since a hole's type is inferred. `--print-after` shows the name as `x#v`, and query
  answers leave such variables out, like the `_a#0` of `%demand`. The lint `hole_capture` (W0007) runs where
  a quote is checked (`TypedQuotes.holeCapture`, for rule and item quotes, not for the rules a module-wide
  directive reifies): a plain variable of a head that no positive atom, equation or aggregate result of the
  body binds, while the body has a hole of type `formula`, a sequence hole or a hole of type `term`
  outside `not`. Holes of type `quoted A` do not count: a typed value is the intended way to share a
  variable. Reports are deduplicated by position, since a quote can be elaborated more than once.
  The probe ran `hugin check` over the 481 programs of `tests/`, `examples/`,
  `docs/design/examples/` and the code blocks of the reference and of `docs/errors`: no W0007, so the lint
  is a warning by default. Changed: `neg/core_e0901_occurs` again (`qvar` adds unknowns to the prelude).
  Goldens `run/tf_qvar`, `run/tf_hole_capture` (with `-A unused_definitions`).
  As in batch 2, the new goldens shift the mutants of the fuzz suites; `MutationFuzzSuite` then met a
  crash of the lexer that predates #96: a `\` at the very end of the input, inside a string, moved past
  the end (`StringIndexOutOfBoundsException`). It is now an unterminated string (E0002), as the reference
  says (`LexerSuite`).

## Glued evaluation (#66, Batch 2)

Design: `docs/design/elaborator-glued.md` (branch `design/elab-66`), section 4.2. A reference to a
definition evaluates to `Val.Top(id, spine, unfolded)`: the definition applied to its spine (applications
and splices), folded, with its value. `force` unfolds it, so every match after `force` sees what it saw
before; `forceMetas` and `quoteFolded` keep it. Folded read-back is used for printing (`showVal`,
`showValPlain`, so diagnostics, hover and goals), for the terms the elaborator keeps (`zonk`, the
inferred types of definitions) and for meta solutions (`psubst`; `unify` solves an unknown against a
`Top` with the folded form first and falls back to the unfolded sides). Everything that computes keeps
using the unfolded `quote`: staging and the handover (`nf`), memo and family keys (`MemoKeys`), the meta
size-change matrices, index unification, the staging observer.

Decisions:

* **The unfolded value is computed eagerly**, not lazily as in smalltt. Evaluation in the core has
  effects: module bodies are generative (an instance per evaluation site) and `Tm.Fresh` advances the
  hygiene counter. A lazy unfolding moved the instantiation of a functor application to whichever later
  item forced it (the first attempt changed the staged output of `a10_meta_applicative` and broke the "a
  definition evaluated once: its uses share the instance" test of `ModulesSuite`). With eager cells the
  unfolded value is computed exactly when evaluation without folding computed it, so staged output is
  identical; the gain is in what is printed and solved, not in evaluation time.
* **Projections unfold**: a member of a module value is shown as the member, as before.
* **Clause functions are not glued**: their applications reduce eagerly through their case trees, as
  before.
* Messages: if expected and found look the same folded, both are printed unfolded; a universe
  inconsistency is printed unfolded (its point is the levels). The E0906 note names the record type as
  written (a signature's name).
* Object typing (#56) forces every value before matching on it, so `core/objtype` needed no change.

## Approximate conversion (#66, Batch 3)

Design: `docs/design/elaborator-glued.md` (branch `design/elab-66`), section 4.3. `unify` takes a
`ConvState`, smalltt's three states. In `Rigid` (the start), two applications of the same definition are
compared by their arguments in `Flex`, and both are unfolded and compared in `Full` if that fails; of two
different definitions the later one (the larger global id) is unfolded first, since a definition refers
only to globals elaborated before it; a definition against anything else is unfolded. `Flex` solves no
meta (`UnifyFailure.FlexSolution`), unfolds no definition and adds no universe level constraint (a level
equation holds there only if the levels are the same). `Full` unfolds at once. In `Rigid` and `Full`, an
unknown against a definition is solved with the folded form, and with the unfolded value if that fails
(Batch 2's rule, now also below an unfolding). Applications of a function defined by clauses that are
stuck keep the approximate comparison by their arguments in every state, as before; the reference now
states that rule (meta/functions, implicit arguments). Type formers, postulates and primitives (the
prelude's `quoted`, `qatom` of #96) are never `Top`s, so nothing unfolds them.

No golden changes: the states decide how much is unfolded on the way, not which programs are accepted
or how their unknowns are solved.

## Notation of the code types (#106)

Decided by the designer in the issue: `^A` spells `⇑A` in ASCII (Kovács's staged elaborator,
`demo/Parser.hs`: `Lift <$> (char '^' *> pAtom)`), an optional explicit staging quote `<t>`, reflection
quotes `'( … )`, and the name `quoted` (Qq's `Quoted`, a Note in the reference's reflection chapter).

* **`^` and `<` by position.** Both are tokens already (`Tok.Caret`, `Tok.Lt`). Where an operand starts
  (`ExprSyntax.parsePrimary`) `^` is the lift and `<` opens a staging quote; between operands they stay
  concatenation and comparison, as `-` is negation or subtraction. Neither starts an argument
  (`startsArg`), so `f ^A` and `f <t>` are binary (`f (<t>)` passes a quote), and neither starts an item
  (`startsItem`), so recovery treats a stray one as before; both start an expression, so that `[x] <t>`
  is a lambda.
* **`<t>`** is `Trees.CodeQuote`, parsed at `LvlHead` (above the comparisons) and closed by `>`;
  `close(open, Tok.Gt)` never finds a `>` by looking ahead (it matches brackets only), so a missing `>` is
  E0005 at the insertion point. Elaboration is Kovács's: checked against `⇑A`, its content is checked
  against `A` at stage 0; inferred, it is `⇑` of the content's type (`Bidirectional`). The printer shows
  `<t>` in surface trees and `⟨t⟩` in elaborated ones.
* **The splice stays `$`** (reference: the Rationale in meta/staging). dtt-rtcg's `Parser.hs` has
  `char '<' *> tm <* char '>'` and `char '~' *> splice`; its `Elaboration.hs` checks `(P.Quote t, VBox a)`
  against `a` and `(P.Splice t, a)` against `□ a`, with inferred staging elsewhere. Neither language has
  comparison operators, so the positional rule is Hugin's own.

Goldens `run/n_staging_notation`, `recovery/r_code_quote`; `ParserSuite`.

**Reflection quotes `'( … )`** (the second pull request). The lexer makes `'` a token before `(` instead of
`{`, `QuoteSyntax.parseQuote` closes the quote with `)`, and the printer, the semantic tokens, completion
inside quotes (`MetaFeatures.inQuote`) and the VS Code grammar follow. `'{` is removed, not kept as an
alias: there are no programs outside the repository. Recovery inside a quote stops at the quote's own
closer: `ParserBase` keeps a stack of body closers (`}` for a module body, `)` for a quote) instead of a
count of bodies, so `skipItem` and `endItem` stop at the innermost one. An unclosed `'(` stays E0005. The
migration of every quote in `std/*.hgn`, the tests, the examples, the reference, the error explanations,
`docs/design/examples` and the current documentation was done by a script that matches each `'{` with its
`}` (skipping strings), and reviewed; the history in `docs/NOTES.md`, `docs/REDESIGN.md`, the design notes
and `docs/PERFORMANCE.md` keeps the syntax of its time. Every check file regenerated identically to the
migrated one.

The new goldens shift the mutants of `RecoveryFuzzSuite`, which then found two recovery gaps older than
this change, fixed at the root:

* a stray token after the period of `%use m.` damaged the `%use` and dropped it, so every name it opens
  was unresolved; `%use` and `%export` are now kept, since their argument is complete
  (`ItemSyntax.damagedItem`; golden `recovery/r_use_stray`);
* the search for a missing delimiter (`ParserBase.closerAhead`) stopped at every token in column 0,
  also at the `}` it was looking for, and at every period at depth 0. It now accepts the delimiter in
  column 0 (a body over several lines ends with `}` there) and passes a period after which no item can
  start (`{ a : t ., b : u }`), so a stray period in a record type over several lines is one error, not
  three (golden `recovery/r_record_stray_period`).

## The reference moves with the language (designer rule, 2026-10-09)

The designer made this a hard rule: no change to the syntax, the semantics or any other part of the
language's definition is merged without the matching change to the language reference, in the same
pull request. The trigger was #56 batch A (PR #93). It changed the static semantics: object code is
checked at the definition of a meta function, `⇑` became covariant, and functor bodies are typed once.
It was merged without touching the reference, and the reference followed only in batch C (PR #94). Splitting
"code" and "docs" into separate batches is not allowed any more: each pull request updates the reference
for what it changes. CONTRIBUTING.md, "Changing the language", states the rule. CI enforces the
mechanical part with `scripts/check-reference-impact.sh`: a pull request that touches `syntax/`, `core/`,
`obj/`, `runtime/`, `Code.scala` or the bundled library must also touch `reference/src/` or
`docs/errors/`, or carry the line `Reference: no change, <reason>` in its description. `CLAUDE.md` repeats
the rule for agents.

## Member functions in module bodies (#100, batch 1)

Design: `docs/design/module-clauses.md`. A declaration `f : A.` of a module body with a meta type and
the clauses `f p̄ = e.` of the same body define a member function (`core/elab/MemberFunctions.scala`).
It is lambda-lifted with the code that `where` blocks used, now shared in `core/elab/Lifting.scala`: a
hidden global named after the member's path (`lib.double`, `tc.step`, `tc.inner.deep` for nested
bodies, from `Modules.hint` and the members being elaborated) over the bound variables of the body's
context. The member is let-bound to the global applied to the context, so the field of each instance is
the shared function applied to that instance, and the clauses are elaborated once per body.

Order: `ModuleBodies.elabMembers` elaborates the members in dependency order, then each member clause
group is a nested block (`Core.inBlock` now saves and restores the frozen metas and the block start, so
blocks nest; after a top-level block the block start stays, as before, for messages printed later), then
the object items. Implementation choices the design did not spell out:

- *Object constants first.* `ModuleBodies.elabMembers` (the one place that orders members, which #91
  batch 2 replaces with per-component ordering, `docs/design/elab-order.md` 5.5 on
  `design/elab-order-91`) runs two phases: the object constants with the definitions they need, then the
  member function signatures with the other definitions. The context member functions are lifted over is
  thus fixed before the first of them, so all take the same leading arguments; the closed type of a
  member function let-binds the definitions elaborated before its signature, and its clauses' prelude
  re-defines the members elaborated before the clause group (all of them, since the groups follow the
  members). An object constant that needs a member function through a definition is left out with that
  error (an unresolved name).
- *Prelude lets.* The leaf of a lifted function re-defines the context's names (`Lifting.prelude`), and
  lets are evaluated when a leaf is: a member definition that calls the function (`limit = bound 2` next
  to `bound`) recursed forever. `Lifting.letBound` (used by `Clauses.leaf`) now leaves out the prelude's
  lets that the leaf does not use. A module value of the body that a member function uses is evaluated
  again at the call (an instance of the call's site, as the design's 4.4 says of bodies on right-hand
  sides).
- *Scope.* A member shadows the file's name in the whole body, also before its declaration, as the
  reference ("Scopes") already said: `ElabState.bodyDeclared` makes a not yet bound member an unresolved
  name, so the item is retried after it. Before, `m = { a : int = two. two : int = 3. }.` with a
  top-level `two` took the file's `two`.
- *Erroneous members.* Every member that is left out (E0907 or another error) is erroneous, as a
  dropped top-level declaration is, so its uses in the body are not reported. A clause group with a
  syntax error leaves its function out silently.
- *Hidden arguments.* `GlobalEntry.hidden` counts the leading arguments of a lifted function; coverage
  messages (`Clauses.missingCase`) and printing (`Printing.liftedApp`) leave them out. This also changes
  `where` functions: ``missing: `f.g (suc _)` `` instead of `` `f.g _ (suc _)` ``, and
  `--print-after elaborate` prints `addTo.go M` instead of `addTo.go K M M`.
- *Signatures only.* A file elaborated for its signatures (`FileEnv.signaturesOnly`) skips member
  clause groups, as it skips top-level clause groups.

Diagnostics: E0105 for a self-referencing member definition (was E0101); E0907 with a subject per case
(refinements, families of object constants, meta inductive families, meta declarations without a
definition or clauses, formula functions defined by rules; the fallback "this item in a module body are
not supported" is gone); E0915 (with a note) for a clause of a function the body does not declare; E0914
for clauses of a body's object constant or definition. Goldens: `run/mc_member_functions` (with
`run/lib/numbers.hgn` for `%export` of a module field), `neg/mc_member_totality`,
`neg/mc_body_unsupported`, `neg/mc_member_clauses`, `neg/mc_where_coverage`.

## The browser build (#58, batch W4)

The compiler is built for the browser by Scala.js without moving sources (the no-move variant of
`docs/design/website.md`, 4.3): the sbt project `web` compiles `src/main/scala` minus the JVM-only packages
`cli`, `repl`, `lsp` and `platform`, plus `web/src/main/scala`. The cross-project layout (W3) can follow
later; the JVM project neither depends on nor aggregates `web`.

- *Platform.* The JS `hugin.platform.Platform` has no file system: `readFile` finds nothing, so an import
  other than `std/` is E0108. The resources (standard library, `docs/errors`, `site-url.txt`) are a Scala
  object generated at build time (`project/BundledResources.scala`), split into literals of 8000
  characters because the Scala.js build still emits class files, whose constants are limited to 64 KB.
  Paths follow `java.nio.file.Path` on Unix.
- *Cancellation.* A deadline (`Platform.deadline`), set from the `budgetMs` option, ends an evaluation at
  its next round with the ordinary "evaluation cancelled" (`cancelled: true` in the result). The
  playground's budget does not need it: the page terminates the worker after 10 s, which stops
  elaboration too.
- *API.* `Hugin.check`, `Hugin.run` (source and options, an object or its JSON text) and `Hugin.phases`
  return JSON text: the `--error-format=json` diagnostics with the lint levels applied, the
  `--print-after` text, the answers (`query`, `vars`, `rows`), the shown relations (`name`, `rows`) and
  `output`, which is what `hugin run` prints on stdout. `Hugin.serveWorker()` is an optional worker
  message loop; the playground's `site/play/worker.js` calls `Hugin` directly. To return rows,
  `Evaluation.Answers` keeps variables and rows (its `lines` are derived from them) and `Result` has
  `relations`; the printed output is unchanged.
- *Linking.* `fullLinkJS` runs the Closure Compiler only for a classic script (`ModuleKind.NoModule`), so
  the bundle is a classic script (a classic worker loads it with `importScripts`); `web/bundle` adds
  `hugin.mjs`, the same code followed by `export { Hugin }`.
- *Guard.* The CI job "Browser build" links with warnings as errors and runs the single-file
  `tests/run` programs (no facts file, no import outside `std/`) and `tests/json` through the bundle in Node
  (`scripts/js-golden.mjs`), comparing with the `.check` files; it prints the bundle's size.
- *Not in the browser yet.* Semantic tokens for highlighting (`hugin highlight` uses `lsp/Tokens`, which
  depends on lsp4j's constants; it needs to move to a shared package first), facts files and multi-file
  programs.
