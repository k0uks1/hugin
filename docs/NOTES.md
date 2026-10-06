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
demanded `A`, so the natural formulation is rejected and one has to write `A >= 1` explicitly
(`tests/run/f_fib_moded.hgn`). Deriving bounds through `A = N - 1` would be a small extension.

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
* **Disjunction inside aggregates** is not supported (E0202); Section 7.2 only splits disjunctions of
  rule bodies.
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

## Possible next steps

* Object-level typing of functor bodies with abstract types (earlier errors for functors).
* Deriving numeric anchors through equations in the termination check.
* Disjunctions inside aggregates via auxiliary relations.
* A faster engine (columnar storage, join planning) behind the same core IR.
