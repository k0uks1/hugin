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
gives `M = {src 1, h (mk 1), mk 1}`, which is not a model: `mk 1 ∈ M` but `r 1 ∉ M`. Since data
constructors never assert (see "Data and fact constructors"), the gap only concerns fact constructors
(`%fact`) built in heads: with `mk` a data constructor the example has no fact `mk 1` and `r` is not
affected.

**Resolved by split rules** (`StratifyPhase.splitRules`). The rule: *if a rule `h … :- B` asserts a
fact-constructor term `c t̄` besides its own fact (a new F-term of its head outside the guarded input
columns, `DepGraph.assertedHeadConstructors`) and `c`'s component comes before `h`'s, the rule
`c t̄ :- B` is added and evaluated in `c`'s component.* (This is how Slog treats nested facts: every
nested fact gets a rule of its own.) The dependency graph already lets `c` depend on everything `B`
reads (Section 6.4 as extended in "Data and fact constructors"), so the split rule has exactly the edges
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

Comparisons with constructor terms are structural, nested terms included (`L = cons 1 nil`); see
"Data and fact constructors".

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
* **Dependency graph.** Section 6.4, with the reads and assertions of "Data and fact constructors"
  (see also the observation above).
* **Engine.** Identities are `(relation, n)` pairs; relations store tuples in insertion order, so
  old/delta/full windows are id ranges. Hash indexes are created for every set of bound columns that
  occurs in a `Scan`. Bodies are executed by backtracking over the IR; aggregates collect one value per
  distinct binding of the aggregate's local variables (Definition 8.4).

## Data and fact constructors

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
recursive calls), the directives of `c` (modes, `%terminates`, `%partial`, `%open`), and the call renamed;
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

## Termination (issue #2, redesign A1)

The termination check (`obj/check/`: `Termination.scala` the phase, `Constructive.scala` constructive rules
and finite sources, `SizeChange.scala` direction (A), `GuardedInduction.scala` direction (B) with measure
inference, `DemandDriven.scala` its case for `%mode`, `Decrease.scala` and `Intervals.scala` the decrease
reasoning, `TerminationFailures.scala` the diagnostics) decides statically
that every recursive component reaches a finite fixed point (docs/REDESIGN.md §4). A recursive component
(Section 6.4) needs an argument only if one of its rules is constructive (Definition 10.1, refined below);
a component with a `%partial` relation is evaluated with the round budget and not checked. Otherwise the
check tries, in this order:

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
never form one thread). The closure of the graphs under composition (at most 4000 graphs, otherwise the
direction fails) is checked: **every idempotent graph `G : p → p` (`G ; G = G`) has a strict arc `i → i`,
or the arc `i =→ i` for every argument `i` of `p`.**

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
components are checked here or `%partial` with a budget; others are finite in their inputs). Plain
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

**Diagnostics.** E0603 names the constructive rule, the cycle through the component, and a measure that
would be accepted (single positions per relation, or a lexicographic pair for a single relation, found by
running the check) or `%partial`. E0604 points at the call (or the demanded call) that fails, labels the
head's or caller's measure, says which slot of the measure fails and whether the decrease or the anchor
is missing, and suggests the missing comparison or `%partial`. Components with a cycle through negation
are skipped (E0601 is reported).

**Not covered.** Measures through non-linear arithmetic other than division by a literal, multiset
orders, declared measure functions, anchors through finite (non-recursive) types, and components that
need (A) for some relations and (B) for others at once (a hand-written demand relation in the same
component as its answer relation, which happens when demand depends on answers; the generated demand of
`%mode` is covered by the demand-driven case). Argument permutations are covered by (A).

## New meta level (redesign Phase B)

The new meta level of `docs/REDESIGN.md` §6 is developed in `hugin.core` alongside the current one and is
not part of the compiler pipeline yet: `hugin check --new-meta f.hgn` elaborates a file, `hugin run
--new-meta f.hgn` prints the elaborated program (meta definitions with the inserted quotes `⟨⟩`, splices
`$` and implicit arguments) followed by the staged object items. The flag is hidden. Golden tests use it
through `.flags` files (`tests/run/core_*`, `tests/neg/core_*`); the mutation fuzzer leaves these files
out of its corpus, since the compiler pipeline does not accept the new syntax.

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
| `core/Staging.scala`, `NewMeta.scala` | staging of object items, the driver |
| `core/CaseTree.scala`, `Matching.scala` | case trees of functions defined by clauses, their reduction with memoisation |
| `core/elab/*` | the elaborator, one trait per concern: `Bidirectional` (dispatch), `Universes`, `PiTypes`, `Applications` (implicit insertion), `Records`, `Operators`, `Coercions` (stage inference), `Names`, `Contexts`, `Declarations`, `Items`, `ObjectItems`, `ElabErrors`; for B2 `Inductives`, `Patterns`, `SplitProblem` (split contexts, index unification), `Clauses` (case trees, coverage), `SizeChange` (termination) |

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
* **Literals (Q2).** A literal checked against a nat-like family (exactly a constant constructor and one
  with a single recursive argument, `zero`/`suc`) is the unary numeral `suc (… zero)`, also in patterns;
  otherwise literals are meta `int`/`float`/`string` values (or object literals at stage 0). Meta `int`
  has no conversion to `nat` yet (a function by clauses on `nat` gives the other direction).

## Possible next steps

* Object-level typing of functor bodies with abstract types (earlier errors for functors).
* A faster engine (columnar storage, join planning) behind the same core IR.
