# Implementation notes before the redesign (historical)

**Historical.** This file keeps the parts of `docs/NOTES.md` that describe semantics the redesign
(issue #40, `docs/REDESIGN.md`) replaced: the milestone status of the definition draft, relation modes
and the built-in demand transformation (with demand per call site and the moded termination case), the
data/fact constructor split, and the decisions of the meta level before Phase B. Nothing here describes the
current implementation. The [language reference](https://k0uks1.github.io/hugin/) is the specification;
`docs/NOTES.md` has the notes that are still current.

The text is unchanged; headings were added where parts were cut out of their sections.


## Status against the milestones of Appendix A.3

| milestone | status |
|---|---|
| 1. Untyped core: parser, core IR, interning store, semi-naive evaluation, stratified negation, output | done |
| 2. Object types and records: declarations, inference, unions and open types, tag tests, named patterns, projection, update | done |
| 3. Arithmetic, aggregates, queries | done |
| 4. Modes and provenance: demand transformation, derivations | done |
| 5. Checks: completeness discipline, termination, `%open` (`%partial` budgets were removed in the redesign, A3) | done |
| 6. Meta level: stage inference, meta evaluator, modules and functors, formula functions, families, monomorphization | done |

All twelve conformance tests of Appendix A.2 are in `tests/` (see the README).

### Moded numeric termination (Definition 10.3)

*Historical: relation modes and the moded termination case were removed in C3 (see "Demand in the prelude").*

The moded numeric case requires the body of a propagation rule to contain `u_k > b` or `u_k ≥ b`
syntactically. With `fib N F :- N > 1, A = N - 1, fib A FA, ...` the bound is on `N`, not on the
demanded `A`, so the natural formulation is rejected. The implementation derives such bounds (see
"Termination" below), and `tests/run/f_fib_moded.hgn` now uses the natural formulation.

### Demand components and termination (Definition 10.3)

*Historical (removed in C3): the generated demand rules are checked by (A)/(B) like any rule.*

Definition 10.3 checks the propagation rules `d(ū) :- d(w̄), …` *of the component of c*. The demand
relation of `c` need not be in that component: `c X Y :- c X Z, Y = Z + 1` with `%mode c + -` gives the
propagation rule `c^d X :- c^d X`, which forms a component of its own; that component has no constructive
rule, and `c`'s component has no propagation rule, so both pass, although `?- c 1 Y` derives `c 1 0`,
`c 1 1`, … forever (`tests/neg/t_termination_demand_loop.hgn`). Likewise a rule of `c` may call a relation
`d` of the component without a measure that reads `c`'s answers (`c X Y :- d X Z, Y = Z + 1` with
`d X Z :- dom X, c X Z`): no demand rule decreases, and the answers grow without new demands
(`tests/neg/t_termination_mutual_unmeasured.hgn`). Both programs were accepted before issue #2; the
check below closes both gaps.

## Implementation decisions of the meta level before Phase B

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

## Disjunction inside aggregates, with the demand transformation (before C3)

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

## Dependency graph (before C3)

* **Dependency graph.** Section 6.4, with the reads and assertions of "Data and fact constructors"
  (see also the observation above).

## Data and fact constructors

*Historical: C3 removed the data/fact split (every constructor is a fact constructor, REDESIGN D1), `%fact`,
E0406 and E0504; this section describes the semantics of PRs A–C before the redesign.*

### Declarations and typing

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

### Semantics

Let F be the plain relations together with the fact constructors and fact structs (and the relations the
compiler introduces: demand, auxiliary and derivation relations), and D the data constructors and data
structs. For a term `t`, `subfact_F(t) = { s ⊑ t | head(s) ∈ F }`: its subterms headed by a member of F,
found by descending through data and fact constructors alike. The immediate consequence operator of a
rule `R` is

```
IC_R(db) = db ∪ ⋃ { subfact_F(Head(R)[v/x]) | db ⊨ Body(R)[v/x] }
```

so a rule adds its head fact and the fact-constructor terms nested in it, also inside data terms. **Data
constructors never assert**: their terms are values only, hash-consed so that equal values have one
identity. Nested data values of input facts are hash-consed, not asserted. Definition 8.7 is unchanged
otherwise (components in order, each to its least fixed point), with the split rules of Proposition 8.8
(a fact term asserted in a head of a later component is also derived in its constructor's component, see
"Nested head constructors and the evaluation order").

* **Patterns** (nested in atoms, or the pattern side of an equation) are structural for D and F: a
  pattern destructures a value and requires no fact; only top-level atoms read facts.
* **Comparisons** (`=` / `<>` tests, ordering) are structural, and no term is absent: `X <> red` holds
  for every `X` but `red`, whether or not `red` was ever built. A data term in a comparison is simply
  built (hash-consed, which has no observable effect). A fact-constructor term that is not a fact is not
  asserted: it evaluates to a `NonFact` word (`ir/IR.scala`), different from every identity and equal to
  a `NonFact` of the same structure; a data term with such a subterm is a `NonFact` too. This is correct
  by the invariant below: a bound value has only facts as fact-constructor subterms, so it is never
  structurally equal to such a term. (A side table of interned non-facts would also work, but an
  identity issued there would differ from the identity the term gets if it becomes a fact later.)
* **Binding equations** `X = c t̄` (`X` unbound, decided by the canonical order): for `c ∈ D` the value
  is built and bound to `X`, so the equation no longer depends on whether the value existed. For
  `c ∈ F` the equation is an existence check, read as `(c t̄ as X)`: it fails if `c t̄` is not a fact
  (`BodyOp.Lookup`). Nested terms combine both: `L = cons (pt N) nil` checks `pt N` and builds the list.
* **Invariant.** Every F-subterm of every value bound in a satisfying valuation is in db. Atoms bind
  facts and their columns, whose F-subterms are facts by `subfact_F`; patterns bind subterms of bound
  values; binding equations check their F-subterms; aggregates bind numbers.
* **E0504, fact constructor built in a moded input.** For every call `p t̄` (positive, under `not`, in an
  aggregate, in a query) with the mode it uses (`Moding.firstApplicable`, as in the demand
  transformation), no input column may contain a fact-constructor term at any depth; variables and data
  terms are fine. The demand rule of the call would build the term as an input, i.e. assert it, so
  `%mode` would change the database. The input columns of a moded relation's own guarded heads are
  patterns (matched against the demand), not constructions: their F-subterms are facts already, so they
  are not checked and asserting them adds nothing. The help suggests removing `%fact` if the constructor
  is only used as a value, or binding an existing fact first (`S = square 4, area S A`).
* **Guarantee.** `%mode` adds facts only to the moded relation and its demand relations: the demand
  rules assert their head (a demand fact), whose inputs contain no F-term construction (E0504), and the
  guarded rules assert what the unmoded rules would, restricted to demanded inputs.

**Dependency graph (Section 6.4).** A body reads the relations of its atoms and, for every binding
equation, the fact constructors on its value side (existence checks). Comparisons, aggregate terms and
patterns read nothing. A head depends on what its body reads, and so does every fact constructor it
asserts (new F-terms outside the guarded input columns); data constructors take no part (they have no
facts, no component and no evaluation round; `CoreProgram.components` leaves them out). The rule
`c t̄ :- body` split off for an asserted `c t̄` has exactly the edges `c → body` (Proposition 8.8).

**Implementation.** `runtime/Store.scala`: one hash-consed table per relation symbol; for F interned
means asserted, so the semi-naive windows are identity ranges and hash indexes hold identities; for D the
table is never scanned and has no indexes. `Engine.eval` has three modes: a dry run (heads check their
arithmetic before interning anything; aggregate terms), body (data terms hash-consed, fact terms looked
up or `NonFact`) and head (every constructor term interned, which asserts the fact ones). The probe
semantics of issue #1, F2 (values versus facts in every relation, probe columns, `Absent`) is gone: its
purpose, `%mode` not adding facts, now follows from data constructors never asserting and E0504. The
type checker example (Section 13.4) keeps its moded `lookup` (`%mode lookup +g +x -t. %terminates g
lookup.`): contexts are data values passed as arguments, not facts to enumerate.

### The prelude

`nil` and `cons` are data constructors, so `len` can no longer match existing `cons`
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
(`tests/run/t_termination_len_callers.hgn`). If the prefix negates or aggregates over a relation that
calls `len`, the shared demand relation would close a cycle through negation; such call sites get their
own demand relation (see "Demand per call site" below).

### Demand per call site

*Historical: the built-in demand transformation and its per-call copies were removed in C3.*

All calls of a moded relation `c` share its demand relation `c^d[m]` (Section 7.3), so the demand rule of
every call depends on its prefix, and `c`'s guarded rules depend on all of them. If a prefix negates or
aggregates over a relation that depends on `c`'s answers, the transformed program has a cycle
`c^d → not x → … → c → c^d` and is rejected (E0601) although the source is stratified:

```
a L N :- e L, len L N.
b L N :- e L, not a L 1, len L N.               (* len^d L :- e L, not a L 1. *)
c M K :- M = count { L | a L _ }, len (cons M nil) K.     (* input from an aggregate over a *)
s L N M :- e L, len L N, C = count { X | f X ; g X N }, V = cons C L, len V M.
```

In the last rule the disjunction's auxiliary relation is moded (its outer variable `N` is an input); its
demand reads the first call of `len`, and the second call's demand reads the aggregate.

**Decision.** `DemandPhase` first transforms with shared demand relations. If a component of the result
has a cycle through negation, every call site of a plain moded relation `c` from a rule of another
relation whose demand rule `c^d[m] … :- prefix` lies in such a component and reads it (the edge of the
cycle that the sharing creates) gets its own copy `c#k` of `c`: the rules of `c` with `c` renamed (also its
recursive calls), the directives of `c` (modes, `%terminates`, `%open`), and the call renamed;
the transformation is repeated (a few rounds, copies are not copied again). The copy has its own demand
relation `c#k^d[m]`, which only that call site and the copy's own recursion feed. If cycles through
negation remain, they are not caused by the sharing and the shared transformation is kept, so the error
(E0601) is reported as before, without copies. Other programs are unaffected: the transformation and
every component are exactly as before (no golden output changed). Pruning the prefix (as for disjunctions
inside aggregates) does not suffice when the call's input is computed by the negated or aggregated part
(`c` and `s` above).

* *Answers.* A copy has the rules of `c`, so for every demand it derives exactly the answers `c` would;
  the call site reads them for its own demands, so its answers are unchanged (the generated fuzz property
  "the demand transformation preserves query answers" and the differential test cover such programs).
* *Stratification.* The copy's demand reads the call's prefix; `c`'s demand, read by the relations the
  prefix negates, no longer depends on it. Copies are created only for call sites on a cycle through
  negation, so programs accepted before keep their components.
* *Termination.* A copy is an ordinary moded relation and is checked by the same conditions (Definition
  10.3 as generalised in "Termination": demand groups, seeds with finite variables): its measure is the
  measure of `c`, its demand group consists of the copy's own propagation rules, and its seed is the call
  site's demand rule, whose inputs must again be terms over finite variables if it reads the copy's
  component. The argument of "Demand-driven components" applies to each copy separately; there are
  finitely many copies.
* `--explain-termination` and `--print-after demand` show the copies (`len[int]#1`); their rules have
  no name, so `%derivations` covers the original relation only.

The fuzz generator (`ProgramGen`) no longer restricts calls of `len` to one per rule and to rules reading
base relations: negations and aggregates in a rule calling `len` may read relations that call `len` (it
favours them, so copies occur in many generated programs). One restriction remains, for termination, not
stratification: such a rule reads *positively* only relations that do not depend on `len`, since a
positive prefix relation joins `len`'s component, where arithmetic or term construction needs a measure
(copies are made only for cycles through negation; making them for every such call would change the
components, and outputs, of accepted programs, e.g. the type checker's `lookup`).
`tests/run/f_demand_per_call.hgn`, `tests/run/f_demand_per_call_disjunction.hgn`.

## Termination: demand-driven components (before C3)

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
   of a finite source outside the component binds it, if it occurs in a *finite column* of an atom of
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
