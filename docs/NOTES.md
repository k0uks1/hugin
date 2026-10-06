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

The value of a constructor term in a comparison is an existing fact (it is looked up, not built). Nested
constructor terms (`L = cons 1 nil`) are now looked up level by level too; before, the inner term was
built without an identity and the comparison never held.

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
* **Staging and instances for tooling.** The typer decides statically where quotes and splices go, but
  the meta evaluator records them in the semantic index (`compiler/SemanticIndex`), because only it knows
  the values: a splice of a primitive is cross-stage persistence (rule Persist) of the literal it
  evaluates to, and code in a functor or formula function has one value per application. Unapplied
  functors therefore have no staging information. Monomorphization records the instance of every family
  use by the span of the application (the reference to the family starts there), and every instance by the
  span of the family's declaration.
* **Suggestions** (`util/Diagnostics`) are edits with a message, attached next to the help that describes
  them in prose. The renderer prints only the help, so diagnostics read the same on the command line;
  the language server maps the edits to quick fixes without knowing any diagnostic code.
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

## Values and facts: probe semantics (issue #1, F2)

Constructing a value asserts a fact (subfact closure), which is what lets created facts trigger rules. The
demand transformation also constructs values, the input arguments of moded calls, so without a
distinction `%mode`, which should only choose an evaluation strategy, added facts to the constructor
relations (`d B (bind G X T1) :- d (lam X T1 B) G` made `bind` facts appear) and changed answers of
queries, negations, aggregates and patterns over them. The implementation separates two notions that
the definition identifies:

* **values** are interned terms with identities; every constructed term is one;
* **facts** are values that belong to the database (asserted).

1. Construction in ordinary rule heads asserts, as before, with the values nested in it (subfact
   closure); created facts trigger rules.
2. Construction in the input columns of demand rules, and in the input columns (of the guarding mode) of
   a moded relation's own rules, only interns: such a value is a **probe**. The demand fact itself, and
   the moded relation's answer, are facts.
3. Nested patterns destructure values structurally; only top-level atoms require facts. For values built
   by ordinary heads the subvalues are facts anyway, so this changes nothing for programs without modes.

Guarantee: `%mode` never adds facts to relations other than the moded relation and its demand relations.
The definition needs four changes: structural matching of nested patterns (no existence condition); the
store invariant "every identity refers to an interned value, and values built by ordinary heads are
facts" instead of "every identity in a fact refers to a fact"; demand rules intern their input terms
without asserting them; probe construction counts as constructive for termination (it invents values).

**Implementation.** `runtime/Store.scala`: each relation keeps all values by identity and, separately,
the identities of its facts in assertion order; scans and their indexes read facts only, and the
old/delta/full windows of semi-naive evaluation are positions in the assertion order, so a probe that an
ordinary head asserts later enters the delta like any new fact. `Deref` and `Lookup` see all values.
`obj/Probes.scala` decides the probe columns of a rule (used by lowering and by the dependency graph).
**Dependency graph (Section 6.4)**: a body depends on the relations of its atoms only, not on constructor
patterns nested in them (structural matching reads no facts); a head constructor adds an edge only if it
is built outside the probe columns (a probe adds no facts). Constructor terms compared with `=` / `<>`
still count, because such a comparison requires the value to exist.

**Consequence for the type checker example (Section 13.4).** Contexts are arguments, not data, so `lookup`
can no longer enumerate `bind` facts; it is moded and terminates structurally on the context:
`%mode lookup +g +x -t. %terminates g lookup.` The termination check now groups a moded component by the
strongly connected components of its demand graph (see "Termination (issue #2)"), because `typed` calls
`lookup` (one way) while the dependency graph joins them through answers.

**Comparisons with terms that were never built.** A comparison with a constructor term (`X <> red`)
looks up the value of `red`. If `red` was never built, it is *absent*: different from every existing
value (`=` is false, `<>` is true) and equal only to an absent value of the same structure (decision on
issue #1, F2). Before, the comparison failed, so whether it could succeed depended on which values
existed — after probes, on whether some demand had built the value, which the evaluation order does not
track. Comparisons are now independent of existence, which amounts to structural comparison. A binding
equation (`X = cons 1 nil` with `X` unbound) still requires the value to exist, since `X` then denotes
it. Implementation: `BodyOp.Lookup(…, orAbsent = true)` for comparison operands yields an `Absent` word,
which occurs only in tests, never in facts.

## Data and fact constructors

**Decision.** Constructors are data by default; facts are opt-in. A declaration `c : τ̄ -> a.` with an
open type `a` declares a *data constructor*: `c t̄` builds a value, but `c` is not a relation. The
modifier `%fact c : τ̄ -> a.` declares a *fact constructor*, which is also the relation of its facts, as
every constructor was before. `%fact` applies in the same way to structs (`%fact s : type = { ... }.`;
a struct without it is a data struct) and to signature fields (`{ t : type, %fact c : int -> t }`). On a
family it applies to every instance (monomorphization copies the flag). The flag is fixed when the
symbol is created (`meta.Sym.fact`, `obj.RelSym.fact`).

**Meta typing.** A data constructor has the meta type `CtorT(τ̄, a)`, written `⇑(τ̄ -> a)`; a fact
constructor keeps `RelT(τ̄, Some a)`, written `%fact ⇑(τ̄ -> a)`. Subtyping:
`RelT(τ̄, Some a) ≤ CtorT(τ̄, a) ≤ Π(⇑τ̄ → ⇑a)`, the latter by the conversion of interface ascription
(`constructorAs`: a constructor matches a value field `dot : shape` or a function field); `CtorT ≰ RelT`,
neither `RelT(_, None)` nor `RelT(_, Some a)`. Columns are invariant, results are checked after
elaboration, as before. A signature field `c : τ̄ -> a` over object types elaborates to `CtorT` and is
matched by both kinds; a field `%fact c : τ̄ -> a` elaborates to `RelT(τ̄, Some a)` and requires a fact
constructor (a data constructor is E0204, with the reason as a note). So inside a functor body only
`%fact` fields can be read.

**E0406, data constructor used as a relation.** Reported by the typer (stage inference of object code,
`meta/typer/ObjectCode`), where the symbol (or the field's meta type) is known: an atom whose relation is a
data constructor or data struct in a body, under `not`, in an aggregate or in a query; a rule head
`c t̄ :- ...`; a directive naming it; and, at the meta level, a data constructor passed where a relation
is expected (`closure { node = shape, edge = square }`). The help suggests `%fact` (with an edit when the
declaration is in the same file). Terms `c t̄` remain allowed everywhere a term is: arguments of heads,
nested patterns, comparisons, aggregate terms, inputs of moded calls. The check runs on source code only:
code the compiler generates later (the guards `(c Z̄ as X)` of the records phase, which lower to `Deref`
and never to `Scan`; demand rules; derivation rules) is not checked and not affected. `--all-relations`
prints facts only: data constructors are not relations, so their values are not listed.

**PR A versus PR B.** This change (PR A) is typing only: evaluation is unchanged, so data constructors
still intern their values and assert them internally (subfact closure, probes, `Absent`, the two-tier
store of "Values and facts" above), but nothing can read them as a relation any more, so the change is
unobservable except through the programs and outputs that had to change. A follow-up (PR B) changes
evaluation: data constructors never assert; probes, `Absent` and the two-tier store go away; a binding
equation with a fact-constructor term checks that the fact exists; E0504 is planned there.

**The prelude.** `nil` and `cons` are data constructors, so `len` can no longer match existing `cons`
facts (`len (cons X L) M :- cons X L, ...`). It is moded instead:

```
len : (l : list A) -> (n : int) -> rel.
%mode len +l -n.
%terminates l len.
len nil 0.
len (cons _ L) M :- len L N, M = N + 1.
```

It computes the length of any list it is given, also of a list that was never asserted:
`?- len (cons "c" nil) N.` now answers `N = 1` (`tests/run/a06_termination_len.hgn`).

**Consequences of a moded `len`.** The demand rule of a call `len L N` is built from the prefix of the
calling rule, so a relation in that prefix that depends on answers of `len` joins `len`'s strongly
connected component (`pick L :- e L, len L N, N < 3.` and `long N :- pick L, len L N.` give the
component `{pick, len, len^d}`). Two refinements of the demand-driven termination check (see
"Termination" below, conditions 1 and 5) accept such components when they are finite
(`tests/run/t_termination_len_callers.hgn`). One limitation remains: if the prefix negates or
aggregates over a relation that calls `len`, the program is no longer stratified after the demand
transformation (E0601), although it is in the source, since all calls share one demand relation. The
same happens within one rule that calls `len` twice with a disjunction inside an aggregate between the
calls (the auxiliary relation's demand reads the first call, the second call's demand reads the
aggregate). The remedy would be demand relations per call site (or a generalisation of the pruning of
demand prefixes of "Disjunction inside aggregates"); the fuzz generator (`ProgramGen`) avoids such
programs: a rule that calls `len` calls it once and reads only base relations.

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
   constructive. Here a head term over variables bound by answers of measured relations is not
   constructive either (`sized (some N) :- e L, len L N`): there are finitely many demands (below), so
   finitely many answers.
2. A rule of a measured relation calls relations of the component only if they are measured, demand
   relations, or unmeasured relations that do not depend on answers of measured relations other than
   through demand relations.
3. Every propagation rule `e^d(ū) :- g^d(w̄), …` whose guard is a demand of a measured relation `g` (in
   any component — the demands of `log2` form their own component), and every propagation rule of the
   component that reads the component, decreases the measure from guard to head: `μ_e(ū) < μ_g(w̄)`,
   decreasing at slot `i`; if slot `i` is an integer, the body bounds `u_i` below (or binds it by relations
   outside the component). Later slots are unconstrained (Ackermann: `ack (M - 1) R1 R` with `R1`
   computed).
4. Conditions 2 and 3 apply per *demand group*: a strongly connected component of the demand graph
   (an edge `g → e` for every propagation rule `e^d … :- g^d …` between measured relations). A
   propagation rule from one group into another needs no decrease, and measures of different groups
   need not have the same shape. The type checker's `typed` (measure `e`) calls `lookup` (measure `g`),
   which never calls back; the dependency graph joins them through answers (`typed` reads `lookup`, whose
   demands come from `typed`'s demands), but their demands form two groups. *Soundness:* order the
   groups topologically; a demand's rank is (position of its group, measure). Every propagation rule
   either stays in its group and decreases the measure, or moves to a later group, so ranks decrease
   lexicographically along demand chains and the argument below applies unchanged.

5. A *seed* of the component — a demand rule without a guard, or guarded by a demand of a relation
   outside the component, that reads the component (the prefix of a call reads relations that depend
   on the callee's answers, see "Data and fact constructors") — demands only values from a finite set:
   every input of its head is a term over *finite variables*. A variable is finite if a positive atom
   of a plain relation outside the component binds it, if it occurs in a *finite column* of an atom of
   the component, or if an equation `X = t` relates it to a term over finite variables. The finite
   columns are a least fixed point: a column of an unmeasured plain relation of the component is finite
   if every rule of the relation puts a term over finite variables (given the columns found so far)
   into it. A column value is a function of the valuation of those variables, each from a finite set,
   so a finite column takes finitely many values over the whole evaluation, whatever else the component
   derives. `u M :- u N, f N M` with `f` moded is rejected (`tests/neg/t_termination_demand_seed.hgn`).

*Soundness.* By condition 3 every chain of demand facts, each derived from the previous one as guard, is
lexicographically decreasing, and the order is well founded on the values that occur: slot 1 never
increases and decreases only to values above a fixed bound, so it decreases finitely often; then slot 2,
and so on (structural slots decrease in the well-founded subterm order). Demands are seeded by finitely
many facts (propagation rules without premises of the component, queries, and seeds by condition 5). By well-founded induction
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
