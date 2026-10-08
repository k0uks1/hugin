# Hugin redesign: Datalog∃! below, a total dependent meta level above

Status: **accepted direction, not yet implemented.** This document is the reference for the redesign. It
is written so that someone who has not followed the design discussion can start implementing it. It
records the decisions taken, the reasons for them, what they replace in the current implementation, an
ordered implementation plan with acceptance criteria, and the questions that are still open.

Related records: issue #1 (the discussion that led here, including the measured impact analyses),
`docs/NOTES.md` (semantics of the current implementation), `docs/INCREMENTALITY.md` (query architecture,
unaffected by this redesign), `docs/LIBRARIES.md` (imports, prelude, interfaces).

Contents

1. Why redesign
2. Decisions at a glance
3. The object level: Datalog∃!
4. Termination as a hard rule
5. Arithmetic: exact and bound columns
6. The meta level: a total, dependent type theory in clause syntax
7. Directives are meta functions
8. Examples (old → new)
9. What happens to the current implementation
10. Implementation plan
11. Open questions
12. Working conventions for this repository
13. References and glossary

---

## 1. Why redesign

### 1.1 The conflict we kept running into

The current language (definition draft rev. 7) combines three features that no other system combines:

1. **Subfact closure** (first-class facts): constructing a term in a rule head asserts it and its nested
   subterms as facts of the constructors' relations.
2. **Modes as an evaluation strategy that must not change answers** (`%mode`, the demand transformation
   of Section 7.3), and which is *load-bearing*: without it, programs such as `fib` with an unbounded
   argument or the moded type checker do not terminate.
3. **Observable constructor relations**: facts of a constructor can be scanned, negated, aggregated and
   queried.

The demand transformation builds the input values of moded calls. With (1) those values become facts;
with (3) programs can see them; so (2) fails: adding `%mode` changes answers. Every complication of the
last months follows from this triangle: probes (values that are interned but not asserted), absent terms
in comparisons, the two-tier store, E0504, the data/fact constructor split, per-call demand copies, the
two directions of termination arguments, and the evaluation-order gap of Proposition 8.8.

The data/fact split (PRs #34–#37) contained the damage, but it did not remove the cause. Every established
system avoids the triangle by giving up one corner:

| system | values are facts | demand changes the database / is needed for termination |
|---|---|---|
| plain Datalog | no value invention at all | no: magic sets is an optimisation |
| Soufflé | no (records/ADTs are values) | no: magic sets is an optimisation; termination is the user's job |
| Slog / "Datalog with First-Class Facts" (DL∃!) | yes | no modes: demand is written as ordinary rules (`eval`, `ck`) |
| Twelf | proof terms, top-down | modes are checked, not a hidden transformation; `%total` proves termination |
| Hugin rev. 7 | yes | yes |

### 1.2 What we learned along the way

* **The paper the language cites already has the answer** (Gilray et al., *Datalog with First-Class
  Facts*, arXiv 2411.14330, §2.3): subfact closure arises only at rule heads, bodies never create anything,
  and demand is ordinary code. Its language DL∃! is Datalog with existentials in heads under a Skolem,
  unique-per-fact reading. Our `%fact` constructors already are exactly that.
* **Datalog alone never gave termination.** Plain Datalog terminates because it has no value invention.
  Once constructors and arithmetic exist, termination needs a checker in any language family. What
  Datalog (bottom-up, set semantics) adds is order-independence, stratified negation and aggregates, and
  automatic termination for the part without invention.
* **Twelf has the right *checking* discipline** (modes, structural termination, coverage, totality),
  but LF as an object level would lose bottom-up set semantics: termination on cyclic data without
  measures, negation, aggregates and query performance. LF ideas belong in the **meta level**.
* **A demand library is impossible on the current meta level** (quoted code is opaque, no recursion, no
  conditionals). It becomes possible with a total meta level that can see object rules as data.
* **Arithmetic needs its own discipline.** Size-change arguments cover `fib`-like recursion on a
  decreasing argument; *bound* (min/max) predicates from Limit Datalog cover shortest-path-like
  recursion through arithmetic, where nothing decreases.

### 1.3 Goals

1. **Termination is a hard rule** at both levels: every accepted program terminates, decided statically.
2. **First-class facts**: every constructed term is a fact with an identity determined by its content.
3. **A small semantic core.** Everything that can be a library is a library: demand, derivations, and
   user-defined program transformations.
4. **Prolog/Datalog syntax at both levels**: declarations and clauses end in `.`, variables are
   uppercase, application is juxtaposition, directives start with `%`.
5. **Nothing hidden**: every transformation is written in Hugin, inspectable (`--print-after`),
   queryable, and checked like hand-written code.

---

## 2. Decisions at a glance

| # | decision | replaces |
|---|---|---|
| D1 | The object level is **Datalog∃!**: Datalog with stratified negation and aggregates, where every constructor is a fact constructor with Skolem identity (existentials in heads). | data constructors, `%fact`, `CtorT`, E0406, E0504, probes/`NonFact`, the value/fact distinction |
| D2 | **No modes at the object level.** Demand is ordinary rules, normally generated by the `%demand` library directive (`%mode` is kept as an alias). | the built-in demand transformation (§7.3), probes, per-call demand copies, moded termination (Def. 10.3) |
| D3 | **Termination by size-change** over derivation chains, in both directions (descent and guarded induction), inferred without annotations. | `%terminates` (kept only as an optional hint), demand groups, seeds/finite variables |
| D4 | **Arithmetic**: exact arithmetic is allowed but recursion through it needs a size-change argument; **bound columns** (`min`/`max`, linear arithmetic, type-consistency) allow recursion through arithmetic with guaranteed termination (divergence becomes ±∞). | `%partial` round budgets for such programs |
| D5 | The meta level is a **total, dependently typed** two-level type theory (2LTT) with an MLTT-style meta level: Π, records/Σ, inductive families, structural recursion, no `Type : Type`. | the 1ML-style meta level (staging inference over Fω-like types, `mod`, applicative/generative module machinery, monomorphization as a separate phase) |
| D6 | The meta level is written in **clause syntax**: `f p̄ = e.` equational clauses, `x : A.` declarations. | `[x] e` lambdas as the main way to define functions (still allowed) |
| D7 | **Stage inference**: quotes and splices are inferred (Kovács-style bidirectional elaboration); users never need `⟨⟩`; `$X` is the explicit splice where wanted (§6.9). | explicit splices in the few places they are needed today |
| D8 | A **reflective embedding** of object syntax (`Term`, `Formula`, `Rule`, `Item`, `Module` as meta inductive types), with reify/reflect coercions inferred from expected types, and **quoted patterns** with `$` holes for matching on object code (§6.9). | nothing (new capability); the opaque `⇑` stays for staging |
| D9 | **Directives are meta functions**: `%d a₁ … aₙ.` applies the meta function `d`. Core directives (`%input`, `%output`, bound columns, `%import`) are primitives of the same kind; `%demand`, `%derivations`, … are prelude code; users can write their own. The directive's type determines its footprint (local `Decl → Decl` vs module-wide `Module → Module`). | the fixed set of built-in directives |
| D10 | Existentials use **Skolem identity**, not labelled nulls; we do **not** adopt wardedness or certain-answer semantics. | — |

---

## 3. The object level: Datalog∃!

### 3.1 Syntax (unchanged where not mentioned)

The object-level surface syntax stays as it is today: object types and constructors, relations, rules,
queries, facts, records/structs, open types, unions, refinements, labels, named and positional
patterns, disjunction, `not`, aggregates, comparisons and arithmetic. Removed: `%mode`, `%terminates`
(see §4.6), `%partial`, `%fact` (every constructor is a fact constructor now), data constructors.

```
expr : type.                      (* an open object type *)
ref : name -> expr.               (* a (fact) constructor: also the relation ⇑(name → expr) *)
lam : name -> typ -> expr -> expr.
edge : node -> node -> rel.       (* a relation *)
path X Z :- edge X Y, path Y Z.   (* a rule *)
?- path a X.                      (* a query *)
```

### 3.2 Values and facts

* **Values** are literals (`int`, `float`, `string`, `bool`) and **identities** of facts.
* Every constructor `c : τ̄ -> a` (with `a` an object type) is the relation ⇑(τ̄ → a): a fact
  `c(v̄)` has the identity `c v̄`, determined by its content (Skolem term, hash-consed). Constructor terms
  are therefore finite trees; the subterm order on identities is well-founded **independently of the
  input** (this is what makes structural termination checkable, §4).
* Relations `r : τ̄ -> rel` have facts without a result identity.

### 3.3 Semantics

Let F be the set of relations and constructors, `subfact(t) = { s ⊑ t | head(s) ∈ F }` (all
constructor subterms of `t`, including `t`).

```
IC_R(db) = db ∪ ⋃ { subfact(Head(R)[v/x]) | db ⊨ Body(R)[v/x] }
```

The meaning of a stratified program is the iterated least fixed point of `IC` per stratum, as in
Section 8 of the definition. Equivalently, a head constructor term `c t̄` is the Skolem existential
`∃Y. c(Y, t̄)` with `Y = c t̄`. Consequences:

* **Bodies never create facts.** A constructor term in a body is a pattern (if its variables are bound
  by it) or an existence check: `X = c t̄` holds iff `c t̄` is a fact. Comparisons are structural; a
  constructor term that is not a fact compares unequal to every value (the `NonFact` marker of PR B
  stays as the implementation of this).
* **Invariant**: every constructor subterm of every value bound in a satisfying valuation is a fact. So
  structural matching of nested patterns and the existence reading coincide.
* **Order independence** (Proposition 8.8): a head that asserts facts of a constructor `c` in a later
  component is split into `c t̄ :- B` evaluated in `c`'s component (already implemented, PR C, #36).
* **Negation and aggregates** are stratified exactly as today (`obj/check/Stratify.scala`).
* **Input facts** may be nested; loading asserts all subfacts.

### 3.4 Object typing

Unchanged: `obj/typing/ObjTyper.scala` (meets, subsumption, unions, open types, refinements, records,
projections, updates, ascriptions), `Moding.scala` keeps computing binding orders and range restriction
(but no longer *modes of relations*; see §3.5).

### 3.5 What "moding" still means

Range restriction (every head variable bound by the body; every negated or compared variable bound
before use) and the canonical binding order of a body are still needed for evaluation. What disappears
is the *mode of a relation* as a semantic notion. Mode *declarations* survive only as arguments of the
`%demand` library directive (§7.4), which uses them to generate rules.

### 3.6 Demand

There is no demand transformation in the compiler. Demand is ordinary rules (Slog's `eval`/`ck` style),
which programs either write by hand or generate with `%demand` (§7.4). Because demand facts and the
values they carry are ordinary facts, nothing about them is hidden: they can be printed, queried and
are termination-checked like any other rule. A magic-sets *optimisation* that provably preserves answers
may be added later (§11, Q9); it is not part of the semantics.

---

## 4. Termination as a hard rule

Every accepted program terminates. The check is static, decidable, and needs no annotations in the
common cases.

### 4.1 Sources of non-termination

Only **value invention** can make a fixed point infinite:

* a head constructor term that is not matched in the body (a new identity), and
* an arithmetic result (`F = FA + FB`, `A = N - 1`) that reaches a head.

A recursive component without invention is finite (classical Datalog). Components with invention need an
argument from §4.2 or §5.

### 4.2 The size-change criterion

Ground values are ordered by two well-founded orders: the **subterm order** on identities (strict:
`t ⊏ c …t…`) and, for integer positions, `<` restricted to values above a lower bound established by a
guard (`N > 1`) or below an upper bound (`N < 100`).

For every rule `H :- …, B, …` where `B` is a recursive body atom (same component), build a *size-change
graph* from the arguments of `B` to the arguments of `H`: an edge `i ↓ j` if head argument `j` is
strictly smaller than body argument `i`, `i ⇊= j` if not larger (Lee, Jones & Ben-Amram 2001). Decrease
is established syntactically: `j` is a proper subterm of the term at `i`; or `j = i - k` with `k > 0` and
a lower-bound guard; etc. (the interval reasoning of `obj/check/Intervals.scala` carries over).

A component with invention is accepted if **one** of the following holds:

* **(A) Descent along derivations.** Every cycle of the size-change graphs (closure, idempotent graphs)
  has a strict decrease `i ↓ i` from body to head. Then every derivation chain through the component is
  finite, so the component is finite. Examples: `check B (bind G X T1) :- check (lam X T1 B) G`
  (`B ⊏ lam X T1 B`), `need A :- need N, N > 1, A = N - 1`.
  *This direction is new*; the current checker rejects these rules (they needed `%partial` in the
  experiments).
* **(B) Guarded induction.** There is an argument position `p` such that (1) along every recursive call
  the body value at `p` is strictly smaller than the head value at `p` (the current Def. 10.3 direction),
  and (2) every rule of the component binds `p` from a relation outside the component or from a finite
  guard (a relation of an earlier component, a constructor fact, a bounded integer interval). Then, by
  well-founded induction on `p`, each value of `p` has finitely many facts, and finitely many values of
  `p` occur. Examples: `typed (lam X T1 B) G (arrow T1 T2) :- check (lam X T1 B) G, typed B … T2`,
  `fib N F :- need N, N > 1, …, fib A FA, fib B FB, F = FA + FB`. This is what
  `obj/check/Termination.scala` implements today for moded components (with lexicographic measures,
  mutual recursion and interval reasoning); it must be re-expressed for unmoded components where the
  guard is an ordinary body atom.

Mixed and mutual components use lexicographic combinations, as the current checker does.

### 4.3 Proof obligations

The implementation must come with a written soundness argument (into `docs/NOTES.md` and, eventually,
the definition):

* (A): an infinite fixed point of a component with finitely many input facts and finitely many rules
  requires derivation chains of unbounded length (König's lemma over the finitely branching derivation
  forest per depth); every such chain contains an infinite descent in a well-founded order —
  contradiction.
* (B): induction on the measure position, using that the guard restricts it to finitely many values.
* Interaction with stratification: a component is checked after the components it depends on, whose
  fixed points are finite by induction.

### 4.4 Diagnostics

A rejected component reports the cycle and the invention site (as E0603 does today) and, when a
decrease exists in only one direction, which direction failed, with a help suggesting a guard
(`N > 0`), a bound column (§5), or `%terminates` as a hint (§4.6).

### 4.5 What the experiments showed

The two programs of §8.1 and §8.2 run on the current compiler only with `%partial` on `check` and `need`
plus `%terminates` hints on `typed` and `fib`. With (A) and (B) as above all four annotations are
inferred. Plain weak acyclicity (Fagin et al.) rejects both programs; it is the special case "no
invention on cycles".

### 4.6 `%terminates` as an optional hint

`%terminates p r.` names the measure position for (B) when inference would be expensive or ambiguous;
it is checked, never trusted. `%partial` (round budgets) is removed: a program that cannot be shown
terminating is rejected.

---

## 5. Arithmetic: exact and bound columns

### 5.1 Exact arithmetic

`+ - * / mod`, comparisons and constant folding stay as today (Section 3.3, `obj/Prims.scala`).
Recursion through exact arithmetic is accepted only with a size-change argument (§4.2), e.g. a
decreasing, lower-bounded argument (`fib`, `len`).

### 5.2 Bound columns (Limit Datalog)

Recursion *through* arithmetic where nothing decreases (shortest paths, longest paths, costs, budgets)
is covered by **bound columns**, following Limit Datalog (Kaminski et al. 2017) and its syntactic variant
*Bound Datalog_ℤ* (Berent, Nissl & Sallinger 2022, §5):

```
dist : (v : node) -> (d : min int) -> rel.   (* the last column is a bound column *)
dist S 0 :- source S.
dist W (D + C) :- dist V D, edge V W C.
```

* A bound column is the **last** column of a relation and is declared `min τ` or `max τ` (τ an integer
  type). The relation keeps, per key (the other columns), only the best value. Semantically a fact
  `dist v k` for a `min` column stands for all `dist v k'` with `k' ≥ k`.
* **Linear arithmetic only** in terms flowing into bound columns: `k₀ + Σ kᵢ·mᵢ` with integer constants.
* **Type-consistency** (Berent et al. Def. 4): a variable with positive coefficient in a `min` head
  column must come from a unique `min` atom of the body (and dually for `max`); comparisons are
  restricted so that they are monotone in the right direction. This guarantees that improving a body
  value can only improve the head value.
* **Divergence becomes ±∞.** Evaluation detects values that would improve forever (a negative cycle for
  `min`, any cycle for `max` with positive weights) via a value-propagation graph and assigns ∞, so
  evaluation always terminates. `∞` is a value of bound columns; `--explain` documents it.
* Bound columns are evaluated with the usual semi-naive loop, replacing a fact when a better value is
  derived (the delta contains improved keys).
* Aggregates `min`/`max` over a bound column are the column itself; `count`/`sum` stay stratified
  (non-recursive), as today.

**The sources, precisely.** Kaminski, Cuenca Grau, Kostylev, Motik & Horrocks (IJCAI 2017, arXiv
1705.06927, §§3–6) and Berent, Nissl & Sallinger (arXiv 2202.05086, §5.1–5.2, which restates the
conditions for Warded Bound Datalog_ℤ and defers the reasoning algorithm to Kaminski et al.):

* *Limit predicates* (Kaminski et al., "Limit Programs"): a numeric predicate has only its last position numeric; a
  *limit* predicate is a `min` or a `max` predicate. A limit fact `B(b̄, k)` says that the value of `B`
  on `b̄` is at most `k` (`min`) or at least `k` (`max`). Interpretations are *limit-closed*: with
  `B(b̄, k)` a `min` (`max`) predicate also holds `B(b̄, k')` for every `k' ≥ k` (`k' ≤ k`). A limit rule's
  head is an object or a limit atom (ordinary numeric atoms are data).
* *Pseudo-interpretations* ("Fixpoint Characterisation") keep one value per limit predicate and object tuple, from
  `ℤ ∪ {∞}`, where `∞` means "holds for every integer" (no bound exists). Rule application
  conjoins the body's comparisons with `ℓ ≤ m` (`min`) or `m ≤ ℓ` (`max`) for each limit body atom
  `B(b̄, m)` with value `ℓ ≠ ∞`; a limit head takes the *optimum* `opt(r, J)` of its term over all
  solutions (`∞` if unbounded) and only the best value is kept.
* *Limit-linear* ("Decidability"): numeric terms are `s₀ + Σ sᵢ·mᵢ` with `mᵢ` distinct variables of limit body
  atoms and `s₀`, `sᵢ` free of them.
* *Type-consistency* (Kaminski et al., "Type-Consistent Programs" = Berent et al. Def. 4), for the semi-grounding (variables not in limit
  atoms replaced by constants) with numeric terms simplified:
  1. every numeric term is `k₀ + Σ kᵢ·mᵢ` with integer `k₀` and **non-zero integer** coefficients `kᵢ`;
  2. if the head is a limit atom `A(ā, s)`, every variable of `s` with a positive (negative) coefficient
     occurs in a **unique** limit body atom of the **same (opposite)** type as the head;
  3. for every comparison `s₁ < s₂` or `s₁ ≤ s₂`, every variable of `s₁` with a positive (negative)
     coefficient occurs in a unique `min` (`max`) body atom, and every variable of `s₂` with a positive
     (negative) coefficient in a unique `max` (`min`) body atom.

  Type-consistent programs are *stable*: if a rule applies, it applies to every
  pseudo-interpretation with better limit values, and its head improves at least as much.
* *Divergence* (Kaminski et al., "Tractability of Entailment: Stability"): the *value propagation graph* `G_P^J` has a node
  per limit fact `B(b̄, ℓ) ∈ J` and an edge `B(b̄) → A(ā)` for every applicable rule with head `A(ā, s)`
  and limit body atom `B(b̄, m)` where `m` occurs in `s`; its weight `μ` is the maximum over such rules of
  `δ = opt − ℓ` (`max → max`), `ℓ − opt` (`min → min`), `−opt − ℓ` (`max → min`), `opt + ℓ`
  (`min → max`), or `opt` if `ℓ = ∞`. For stable programs, every node on a **positive-weight cycle** has
  value `∞` in the least fixpoint (their soundness lemma). Their Algorithm 1 alternates immediate consequence with
  replacing the values of nodes on positive-weight cycles by `∞`; it terminates (without a new
  edge or a new positive cycle the values converge within `O(|P|²)` rounds of the semi-ground program, and edges and cycles are added only polynomially often) and is correct.

**In Hugin.** Rules as above, adapted to relations, stratification and the termination check:

* **Declaration.** `min τ` / `max τ` is allowed only as the type of the **last** column of a **relation**
  declaration (not a constructor, Q4), with `τ` an integer type (`int` or a refinement of it), and not on
  a `%mode`d relation. Other uses are E0605.
* **Reading a bound column.** A body atom of a bound relation binds its bound column to the **best**
  value of the key (the pseudo-interpretation reading). The bound-column argument of such an atom must be
  a variable or `_`.
* **Type-consistency (E0606)** applies to the *limit variables* of a rule: variables bound by the bound
  column of a positive body atom of a bound relation **of the head's component**. Bound relations of
  earlier components are complete when the rule runs, so their values are constants of the
  semi-grounding (they may be used freely, like the result of an aggregate). For limit variables:
  * each occurs in exactly one positive atom (its bound column); not in other columns, not in another
    bound atom, not under `not` or in an aggregate;
  * each occurrence elsewhere is in a *linear* term: `+`, `-`, unary `-` and multiplication by an integer
    literal; after simplification its coefficient is non-zero; a variable `X` defined by a binding
    equation `X = t` is replaced by `t`;
  * in the head: only in the bound column of a bound head relation, with conditions 2 above (`min` head:
    positive coefficient from `min` atoms, negative from `max` atoms; dually for `max`);
  * in comparisons: only `<`, `<=`, `>`, `>=` (with `a > b` read as `b < a`), with condition 3 above;
    never in `=` or `<>` tests.
* **Evaluation.** A bound relation stores one tuple per key; deriving a better value replaces it (the
  semi-naive delta contains the improved keys). Each component with bound relations runs Kaminski et al.'s
  Algorithm 1 with the check spaced out: after rounds 4, 8, 16, …, the value propagation graph is built
  by one pass over the component's rules (edges from limit atoms whose variable occurs in the head's bound
  term, weights as above), and every node reachable from a positive-weight cycle (Bellman–Ford with
  maximisation) gets the value `∞` (`-∞` for `min`, `+∞` for `max`) — nodes reachable from a cycle would
  become `∞` by propagation anyway. Since a positive cycle, once present, stays (stability), checking at
  growing intervals preserves termination.
* **∞** is a value of integer columns: `-∞ < k < +∞`; `∞ ± k = ∞`, `k·∞ = ±∞` for `k ≠ 0`, `∞ / k = ±∞`;
  `∞ − ∞`, `0·∞` and `∞ / ∞` are undefined (a rule does not fire, as on overflow). Type-consistency
  ensures that a type-consistent rule never meets an undefined case. It prints as `∞` / `-∞`.
* **Termination** (§4): the bound column of a bound head is not value invention (its values are kept
  finite per key by the divergence check); the key columns are checked as usual, so a component whose
  invention is only through bound columns is accepted.

**Not adopted**: wardedness and labelled nulls (D10). Whether Berent et al.'s complexity results carry
over to Skolem existentials is open (§11, Q4); our existentials are restricted by §4 instead.

---

## 6. The meta level: a total, dependent type theory in clause syntax

### 6.1 Overview

The meta level is a two-level type theory (2LTT, Annenkov, Capriotti, Kraus & Sattler; for staging:
Kovács, *Staged Compilation with Two-Level Type Theory*, ICFP 2022). The **outer level** is a total
dependent type theory evaluated at compile time; the **inner level** is the object level of §3. The
meta level computes object programs; it never runs at evaluation time.

### 6.2 Universes and classification

* `type` — the universe of **object types** (2LTT's U₀). `expr : type.` declares an open object type,
  as today.
* `Type` — the universe of **meta types** (U₁). `nat : Type.` declares a meta type.
* `rel`, `prop` — object relation and formula results, as today.

A constructor declaration is classified by the universe of its result:

| declaration | result in | meaning |
|---|---|---|
| `suc : nat -> nat.` | `Type` | meta constructor (inductive meta type) |
| `lam : name -> typ -> expr -> expr.` | `type` | object (fact) constructor |
| `edge : node -> node -> rel.` | `rel` | object relation |
| `f : nat -> int.` with clauses `f … = … .` | `Type` | meta function |

Universe levels: the meta level needs `Type`-valued signatures (modules containing types), so signatures
live one level up. Start with a predicative hierarchy `Type₀ : Type₁ : …` whose levels are inferred and
never written (§11, Q1). `Type : Type` is excluded: it breaks totality.

*Implementation note (Phase B1):* `⇑A : Type₀` for every object type `A`, including `type` itself, so a
signature whose components are object types and relations is in `Type₀`; only signatures with meta-type
components (`{ t : Type }`) live one level up. Levels are inferred, cumulative and global to a program
(no universe polymorphism). See `docs/NOTES.md`, "New meta level (redesign Phase B)".

### 6.3 Core calculus

* Π types `(x : A) -> B`, implicit `{x : A} -> B` (inferred by higher-order pattern unification).
* Records / Σ types `{ l₁ : A₁, l₂ : A₂ }` with dependent fields; record values `{ l₁ = e₁, … }`;
  projections `e.l`. Module signatures are record types; modules are record values; functors are
  functions.
* Inductive families declared by constructor declarations into a `Type`, strictly positive
  (positivity check).
* Literals and primitive operations on `int`, `string`, … at the meta level (shared with the object
  level's primitives).
* The staging types: `⇑A` (object terms of type `A : type`), `⇑(τ̄ → rel)` (object relations),
  `⇑prop` (object formulas), `⇑items` (object declarations and rules). These are **opaque**: they can be
  spliced, not inspected.
* The reflective types of §6.8 (`Term`, `Formula`, `Rule`, `Item`, `Module`): inspectable data.

### 6.4 Syntax: clauses

Functions are defined by equational clauses with uppercase pattern variables; types are declared with
`:`. All items end in `.`; `(* … *)` comments.

```
nat : Type.
zero : nat.
suc : nat -> nat.

plus : nat -> nat -> nat.
plus zero N = N.
plus (suc M) N = suc (plus M N).

vec : Type -> nat -> Type.
vnil  : vec A zero.
vcons : A -> vec A N -> vec A (suc N).

head : vec A (suc N) -> A.          (* coverage: vnil is impossible here *)
head (vcons X _) = X.
```

* Variables in clauses are implicitly bound (as in rules); free uppercase variables in declarations are
  implicit Π-binders (as for families today).
* `[x] e` lambdas remain for inline functions.
* Definitions without clauses: `x : A = e.` as today; `x = e.` with inferred type.
* Pattern matching is by clauses only (no `case` expression in the first version; §11, Q7).
* **Local definitions** (Haskell-style `where`): a clause's right-hand side may be followed by a `where`
  block of bindings, each ending in `.` (the last one ends the clause). The bindings scope over the
  right-hand side and over each other in source order, and see the clause's pattern variables. They are
  simple definitions (`x = e.`, `x : A = e.`), local functions (`f : A.` followed by its clauses, checked
  for coverage and termination like top-level functions; no general recursion), or irrefutable pattern
  bindings (`c x̄ = e.`, a constructor pattern binding the names `x̄`; a refutable pattern is a coverage
  error). A `where` block is elaborated to `let` bindings and lambda-lifted local functions, not to new
  core syntax. Layout: the block consists of the items after `where` that start at a column greater
  than the clause's first column; it ends before the next item at that column or less (for top-level
  clauses: the next item at column 0), at `}` or at the end of the file.

```
area : shape -> int.
area (rect W H) = w * h
  where w = abs W.
        h = abs H.

fibPair : nat -> pair int int.
fibPair zero = mkPair 0 1.
fibPair (suc N) = mkPair b (a + b)
  where mkPair a b = fibPair N.          (* irrefutable pattern binding *)
```

### 6.5 Totality

* **Coverage**: the clauses of a function must cover all constructors of the matched inductive types,
  taking index unification into account (`head` above needs no `vnil` clause).
* **Termination**: structural recursion, checked with the same size-change machinery as §4.2 (on meta
  constructor terms). No general recursion, no `Type : Type`, strict positivity.
* Consequence: elaboration and expansion of every program terminate.

### 6.6 Stage inference

Users never write quotes or splices. The elaborator is bidirectional; when the expected type is at the
object stage and the inferred one is at the meta stage (or vice versa), it inserts a quote or splice, as
in Kovács's elaborator. Hugin's current typer already performs this inference for its stages
(`meta/typer/ObjectCode.scala`); the new elaborator generalises it to the dependent setting.

### 6.7 Modules, functors, families, formula functions

All of these become ordinary meta-level programming:

* **Modules** are record values; **signatures** are record types; **functors** are functions from
  records to records; `%import "f"` yields a module value (`docs/LIBRARIES.md` stays valid).
* **Ascription** (`m : sig = e.`) is record subtyping with coercion, transparent by default; the current
  interface rules (constructor fields, hiding) become instances of it. Sealing (opaque ascription) is a
  later extension (§11, Q8).
* **Generativity**: a module body `{ … }` creates fresh object relations each time it is evaluated, as
  today (`r1 ≠ r2` in A.2 (10)).
* **Families** (`list A`, `len[int]`) are meta functions returning object types and relations; their
  applications are **memoized by normalised arguments**, which gives applicative sharing (one instance
  of `len` per type). This replaces the separate monomorphization phase.
* **Formula functions** are meta functions returning `⇑prop`; hygiene renames object variables at each
  application, as today.

### 6.8 The reflective embedding

For transformations such as demand, object syntax must be **data**. The prelude defines inductive meta
types:

```
Term    : Type.   (* variables, literals, constructor applications, arithmetic *)
Formula : Type.   (* atoms, negation, comparisons, aggregates, disjunction *)
Rule    : Type.   (* head + body *)
Decl    : Type.   (* object type, constructor, relation declarations with their directives *)
Item    : Type.   (* Decl | Rule | Query *)
Module  : Type.   (* a list of items with its scope *)
```

Object relations, constructors and types appear in this syntax as **references** (`⇑(τ̄ → rel)` values),
so reflected programs cannot refer to undeclared names. Object variables are represented by **names**
(locally nameless where binders occur, e.g. aggregates); reflection renames them hygienically.

* **Reify** (implicit): object syntax written where a value of a reflective type is expected is turned
  into data: `typed_rules : List Rule = [ typed (ref X) G T :- lookup G X T, … ].`
* **Reflect** (implicit): a value of type `Module`/`List Item` in an item position is turned back into
  object items; reflected items are **re-elaborated and re-checked** at the object level (typing,
  stratification, termination). Generated items carry the span of the source item they derive from and
  a provenance note (`in expansion of %demand`).
* The opaque `⇑` staging (§6.3) remains for ordinary code generation; reflection is only needed by
  programs that inspect object syntax.

### 6.9 Quoted patterns and holes

Meta functions can **pattern-match on object code** by writing the pattern in object syntax, as with
Scala 3's quoted patterns (`case '{ $x + $y } =>`) or Lean's `` `($a + $b) `` patterns. (MetaOCaml is
deliberately generate-only: its code values are opaque, like our `⇑`.) Quoted patterns are syntax over
the reflective embedding of §6.8; the opaque `⇑` can still only be spliced, never matched.

Notation (decided): **`$`** marks holes, Scala-style.

* In a **pattern** whose expected type is reflective (`Term`, `Formula`, `Rule`, `Item`, `Module`),
  object syntax is reified by expected type (no quote marker); `$X` binds the meta variable `X` to the
  subterm at that position; `$..Xs` binds a sequence (body formulas, arguments, list items).
* In an **expression**, `$X` / `$..Xs` splice a meta value (or sequence) into object syntax. Splices are
  normally inferred (§6.6); `$` is the explicit form, needed only where inference is ambiguous or for
  readability, and it is the same notation as in patterns.
* A plain uppercase `X` inside a quoted pattern matches an **object variable**; `$X` in a variable
  position binds that variable's name (a meta value of type `Var`).
* Names of relations, constructors and types in patterns **resolve to symbols** in scope: `typed $E $G $T`
  matches atoms of the relation `typed` in scope, not the text `typed`. Matching is therefore hygienic and
  stable under renaming and shadowing.
* **Binders** (aggregates `count { V | … }`, formula functions) use higher-order holes as in Scala 3:
  `$F[V]` matches a formula that may mention the locally bound `V`; with locally nameless
  representation (Q5) this is well defined.

Examples:

```
(* swap the arguments of a binary atom *)
flip : Formula -> Formula.
flip ($R $X $Y) = ($R $Y $X).

(* the core step of %demand for one relation: guard its rules, propagate demand to recursive calls *)
guard : Rule -> List Rule.
guard (typed $E $G $T :- $..Body) =
  (typed $E $G $T :- typed.check $E $G, $..Body)
  :: propagate (typed.check $E $G) Body.
guard R = [R].                                   (* all other rules unchanged; coverage needs it *)

propagate : Formula -> List Formula -> List Rule.
propagate Pre [] = [].
propagate Pre (typed $E2 $G2 $_ :: Rest) = (typed.check $E2 $G2 :- $Pre) :: propagate Pre Rest.
propagate Pre (F :: Rest) = propagate ($Pre, $F) Rest.
```

Elaboration and checking:

* Quoted patterns elaborate to ordinary **constructor patterns** over the reflective inductive types, so
  coverage checking (§6.5: `guard R = [R].` is required), structural termination (recursion on `Rest`)
  and stage inference apply unchanged.
* **Typing, first version**: holes have untyped reflective types (`$E : Term`, `$Body : List Formula`);
  reflected results are re-checked at the object level (§6.8).
* **Typing, later** (Q5): with typed reflection (`Term τ` indexed by object types), `typed $E $G $T` gives
  `E : Term expr`, `G : Term ctx`, `T : Term typ`, and generators are well-typed by construction, as in
  Scala 3. The surface syntax does not change.
* Diagnostics for generated rules keep pointing at the source items (provenance, §6.8).

---

## 7. Directives are meta functions

### 7.1 The rule

```
%d a₁ … aₙ.          (standalone)
%d a₁ … aₙ  DECL      (prefix: applies to the declaration that follows)
```

`%d` resolves `d` like any name (prelude, imports, the current module). Its arguments are elaborated
against `d`'s parameter types (with stage inference and reification), and `d` is applied. Its result type
determines what happens:

| type of `d a₁ … aₙ` | footprint | effect |
|---|---|---|
| `Decl -> Decl` | local | rewrites the declaration it is attached to (prefix form) or names (standalone) |
| `Module -> Module` | module-wide | rewrites the enclosing module body (needed when call sites change) |
| `List Item` | additive | inserts items |

Expansion happens in **source order**, each directive seeing the output of the previous ones. Totality
of meta functions guarantees that expansion terminates; the result is elaborated and checked like
hand-written code. The footprint tells the incremental compiler what depends on what
(`docs/INCREMENTALITY.md`): local directives keep per-item incrementality, module-wide ones make the
module's items depend on the expansion.

Unknown directives are name errors with suggestions (as E0103 is today). Argument errors are type
errors; dependent typing lets directives check, e.g., that mode labels match the relation's columns.

### 7.2 Primitive directives

Implemented in the compiler, typed like any directive:

* `%input r.`, `%output r.` — I/O relations.
* `%import "path"` — a module value (an expression form rather than a directive, as today).
* bound columns (`min τ`, `max τ`) are a type form, not a directive.
* `%infix op p.` — parsing (handled before elaboration, as today).
* `%terminates p r.` — termination hint (§4.6).
* `%complete r.` — the completeness discipline (Section 6.5), unchanged.

### 7.3 Library directives (prelude)

* `%demand r m.` — the demand transformation (§7.4). `%mode` is an alias for backwards compatibility.
* `%derivations r.` — derivation relations (Section 7.4 of the definition; today
  `obj/transform/Derivations.scala`).
* Users can define further directives, e.g. `%symmetric r.` adding `r Y X :- r X Y.`

### 7.4 `%demand`

```
demand : (r : ⇑(τ̄ → rel)) -> Modes r -> Module -> Module.
mode = demand.                      (* alias *)
```

`Modes r` is indexed by `r`'s columns, so `%demand typed +e +g -t.` is checked against `typed`'s labels.
The function implements the magic-sets transformation of today's `obj/transform/Demand.scala`
(Section 7.3): for each call site of `r` with the given inputs bound, a demand relation `r.check` (named
by the library) receives the input values, the rules of `r` are guarded by it, and propagation rules
pass demand to recursive calls. Because the generated demand rules build ordinary facts (contexts
become `bind` facts, numbers become `need` facts), termination is checked by §4 on the generated rules:
descent (A) for the demand relation, guarded induction (B) for the answer relation.

`demand` must also rewrite call sites outside `r`'s own rules (the seed rules), hence its
`Module -> Module` type.

---

## 8. Examples (old → new)

The "new" programs of §8.1 and §8.2 were run on the current compiler (after PRs #34–#37) in their
hand-written form; they give the same answers as the old programs, with `%partial`/`%terminates`
annotations that the new checker infers (§4.5). The files are reproduced here; they can be added to the
test suite as the first goldens of the redesign.

### 8.1 Structured runtime data: the type checker

Old (`examples/typechecker.hgn`): contexts are data values, built invisibly by the demand
transformation.

```
ctx : type.   empty : ctx.   bind : ctx -> name -> typ -> ctx.

lookup : (g : ctx) -> (x : name) -> (t : typ) -> rel.
%mode lookup +g +x -t.
%terminates g lookup.
lookup (bind _ X T) X T.
lookup (bind G Y _) X T :- lookup G X T, X <> Y.

typed : (e : expr) -> (g : ctx) -> (t : typ) -> rel.
%mode typed +e +g -t.
%terminates e typed.
typed (ref X) G T :- lookup G X T.
typed (lam X T1 B) G (arrow T1 T2) :- typed B (bind G X T1) T2.
typed (app F A) G T1 :- typed F G (arrow T0 T1), typed A G T0.

result E T :- program E, typed E empty T.
```

New, with the library directive: **the same program**, with `%demand` (or `%mode` as alias) now meaning
"generate the demand rules", and no `%terminates`:

```
%demand lookup +g +x -t.
%demand typed +e +g -t.
```

New, hand-written (what `%demand` generates, up to naming), all constructors are facts:

```
check : (e : expr) -> (g : ctx) -> rel.
check E empty :- program E.
check B (bind G X T1) :- check (lam X T1 B) G.        (* (A): B ⊏ lam X T1 B *)
check F G :- check (app F _) G.
check A G :- check (app _ A) G.

lookup (bind G X T) X T :- bind G X T.                 (* contexts are facts: a scan *)
lookup (bind G Y U) X T :- bind G Y U, lookup G X T, X <> Y.

typed (ref X) G T :- check (ref X) G, lookup G X T.
typed (lam X T1 B) G (arrow T1 T2) :- check (lam X T1 B) G, typed B (bind G X T1) T2.   (* (B) on e *)
typed (app F A) G T1 :- check (app F A) G, typed F G (arrow T0 T1), typed A G T0.

result E T :- program E, typed E empty T.
```

Differences: the input file is unchanged (nested terms; loading asserts subterms). Contexts are facts
(`--all-relations` lists `bind empty "x" (base "int").`), so they can be queried and aggregated. Demand is
visible code.

### 8.2 Arithmetic in recursion: `fib`

Old (`tests/run/f_fib_moded.hgn`):

```
fib : (n : int) -> (f : int) -> rel.
%mode fib +n -f.
%terminates n fib.
fib 0 0.
fib 1 1.
fib N F :- N > 1, A = N - 1, B = N - 2, fib A FA, fib B FB, F = FA + FB.
?- fib 90 F.
```

New, with the library: `%demand fib +n -f.` in place of the two directives. Hand-written:

```
need : (n : int) -> rel.
need 90.
need A :- need N, N > 1, A = N - 1.                    (* (A): A < N, N > 1 *)
need B :- need N, N > 1, B = N - 2.

fib : (n : int) -> (f : int) -> rel.
fib 0 0.
fib 1 1.
fib N F :- need N, N > 1, A = N - 1, B = N - 2, fib A FA, fib B FB, F = FA + FB.   (* (B) on n *)
?- fib 90 F.
```

Compile-time alternative (total meta function; no runtime recursion):

```
fibm : nat -> int.
fibm zero = 0.
fibm (suc zero) = 1.
fibm (suc (suc N)) = fibm N + fibm (suc N).

fib : int -> int -> rel.
fib 90 (fibm 90).            (* stage inference splices the compile-time value; 90 : nat by literal overloading *)
```

### 8.3 Recursion through arithmetic without descent: shortest paths

No current equivalent (needs `%partial` today):

```
node : type.
edge : node -> node -> int -> rel.
source : node -> rel.
%input edge.  %input source.

dist : (v : node) -> (d : min int) -> rel.
dist S 0 :- source S.
dist W (D + C) :- dist V D, edge V W C.
%output dist.
```

Terminates for every input; a negative cycle yields `dist v -∞`.

### 8.4 A functor in the new meta level

Today (`tests/run/a10_meta_applicative.hgn`):

```
graph : Type = { node : type, edge : node -> node -> rel }.
tc (g : graph) = {
  path : g.node -> g.node -> rel.
  path X Y :- g.edge X Y.
  path X Z :- g.edge X Y, path Y Z.
}.
```

New: the same text. `graph` is a record type in `Type₀` (its components are object types and relations,
and `⇑type : Type₀`; see §6.2) (`mod` disappears as a separate universe), `tc`
a function returning a module (record) value; the body is generative.

### 8.5 A user-defined directive

```
symmetric : (r : ⇑(A -> A -> rel)) -> List Item.
symmetric R = [ R Y X :- R X Y ].

friend : person -> person -> rel.
%symmetric friend.
```

---

## 9. What happens to the current implementation

Package by package (sizes are current line counts).

| package / file | fate |
|---|---|
| `util/`, `syntax/` (lexer, parser, slices, printer, TreeOps) | **keep**; extend the parser for meta clauses `f p̄ = e.`, `Type`, `min`/`max` column types, directive-as-application |
| `compiler/` (phases, CompilationUnit, Libraries, ProgramElab, SemanticIndex) | **keep**; the phase plan changes (§10); `ProgramElab`'s per-item queries apply to the new elaborator |
| `query/` (Database, CompilerQueries, Ide, FileDiagnostics), `lsp/`, `repl/`, `cli/` | **keep** (incremental architecture of `docs/INCREMENTALITY.md` is independent of the semantics) |
| `meta/Namer.scala`, `Symbols.scala`, `Keys.scala`, `SymTable.scala` | **adapt** (stable keys stay; symbol kinds change) |
| `meta/typer/*` (≈2,000 lines), `meta/MTrees.scala`, `meta/MetaEval.scala`, `meta/Monomorphize.scala` | **rewrite** as a dependent elaborator (bidirectional, normalisation by evaluation, higher-order pattern unification, stage inference, coverage and totality checking, reflection); Kovács's elaboration-zoo is the reference design |
| `obj/typing/ObjTyper.scala`, `TypeOps.scala`, `ConstFold.scala` | **keep** |
| `obj/typing/Moding.scala` | **keep** for binding order and range restriction; remove relation modes |
| `obj/typing/Directives.scala`, `obj/ProgramFacts.scala` | **adapt**: only primitive directives remain |
| `obj/transform/Demand.scala` (304) | **delete** after `%demand` exists as a prelude function |
| `obj/transform/Derivations.scala` | move to a prelude directive (or keep as a primitive at first) |
| `obj/transform/Records.scala`, `Disjunctions.scala` | **keep** |
| `obj/check/Stratify.scala` (incl. split rules), `Completeness.scala`, `DependencyGraph.scala` | **keep** (remove data/fact distinctions) |
| `obj/check/Termination.scala` (836), `Intervals.scala` | **rework** into the size-change checker of §4 (reuse interval reasoning and the measure search) |
| `ir/`, `runtime/` | **keep**; remove the data-constructor table kind; add bound columns (best-value relations, ∞) |
| data/fact split (`CtorT`, `%fact`, E0406, E0504, `RelSym.isData`, `NonFact` for data) | **delete** (all constructors are facts); keep `NonFact` for never-built fact terms in comparisons |
| `src/test/scala/hugin/fuzz` (ProgramGen, NaiveEvaluator) | **adapt**: the naive evaluator implements §3.3 + §5; the generator drops modes and emits bound columns |

Definition chapters affected: §3 (meta types), §4 (modules → dependent records), §4.6 (monomorphization →
memoised staging), §6.3 (moding), §7.3 (demand → library), §10 (termination), new sections for bound
columns, directives-as-meta-functions and reflection.

---

## 10. Implementation plan

Each step is one or more PRs into the development branch, keeps CI green, and lists its acceptance
criteria. Steps within a phase are ordered; phases A and B can proceed in parallel.

### Phase A — object level, on the current meta level

**A1. Size-change termination, both directions.** Extend `obj/check/Termination.scala` with
direction (A) (§4.2) and re-express (B) for unmoded components guarded by ordinary atoms.
*Accept*: `check`/`need` (§8.1, §8.2 hand-written) are accepted without `%partial`; `typed`/`fib`
without `%terminates`; every currently accepted program stays accepted; the negative termination tests
stay rejected; soundness notes in `docs/NOTES.md`; new goldens for §8.1/§8.2 hand-written forms.

**A2. Bound columns.** Parser (`min τ`/`max τ`), typing (last column, integer type), type-consistency
check (new error code), engine support (best value per key, ∞ by divergence detection), naive
evaluator. *Accept*: §8.3 runs; negative cycles give ∞; type-inconsistent programs are rejected with
precise diagnostics; fuzz generator emits bound columns.

**A3. `%partial` removal.** Programs needing it are either accepted by A1/A2 or rejected. *Accept*:
`a07_partial_*` tests are rewritten (accepted forms or negative tests).

### Phase B — the new meta level

**B1. Core elaborator.** A new package (e.g. `hugin.meta2` or `hugin.core`) with: core syntax,
values/NbE, bidirectional checking, implicit arguments via higher-order pattern unification, universes
`type`/`Type_i`, Π, records, stage inference with `⇑`. Developed alongside the old meta level, behind a
flag. *Accept*: unit tests of the core; the README examples that use only these features elaborate.

**B2. Clauses, inductive families, totality.** Parser for meta clauses; positivity; coverage with index
unification; structural termination via the §4.2 machinery. *Accept*: `nat`, `vec`, `plus`, `head`,
`fibm` (§6.4, §8.2) elaborate; incomplete or non-terminating meta functions are rejected with
diagnostics.

**B3. Port modules, functors, families, formula functions, imports.** Generative module bodies,
memoised families, hygiene, ascription and interfaces. *Accept*: every current golden test produces the
same output (diagnostic texts may change; each changed `.check` is reviewed and listed); then the old
meta level (`meta/typer`, `MetaEval`, `Monomorphize`) is deleted.

### Phase C — reflection and directives

**C1. Reflective embedding.** Prelude types of §6.8, reify/reflect coercions, re-elaboration of
reflected items with provenance spans, quoted patterns and `$`/`$..` holes (§6.9), elaborated to
constructor patterns. *Accept*: round-trip tests (reify ∘ reflect = id up to renaming); `flip`, `guard`
and `propagate` of §6.9 elaborate and pass coverage and termination; matching resolves names to symbols
(a shadowed `typed` does not match); higher-order holes for aggregates; diagnostics in generated code
point to source items.

**C2. Directives as meta functions.** Resolution, argument elaboration, footprints, source-order
expansion; primitive directives re-expressed. *Accept*: `%symmetric` (§8.5) as a user directive;
unknown directives give name errors; incremental tests show local directives keep per-item reuse.

**C3. `%demand` in the prelude; `%mode` alias.** *Accept*: the type checker (§8.1) and `fib` (§8.2) run
with `%demand`/`%mode` and give the old answers; the generated rules are visible with `--print-after`;
then `obj/transform/Demand.scala`, relation modes, per-call copies and the data/fact split are deleted;
all constructors are fact constructors.

### Phase D — consolidation

Rewrite `docs/NOTES.md`, the README language summary and the conformance tests (Appendix A.2) for the new
semantics; update `docs/LIBRARIES.md` and the prelude; close the redesign in issue #1.

---

## 11. Open questions

Each has a recommendation; decisions belong to the language designer.

* **Q1 Universe levels.** Inferred cumulative hierarchy vs. two fixed universes (`Type` for values,
  `Type₁` for signatures). *Recommendation*: start with inferred levels, no user syntax.
* **Q2 Literal overloading.** `90 : nat` vs `90 : int` (§8.2). *Recommendation*: meta `int` with a total
  conversion; `nat` literals by expected type.
* **Q3 Precise size-change rules.** Which syntactic forms establish decrease (subterm, `N - k` with
  guard, intervals, lexicographic tuples); whether to implement full SCT closure or the current
  measure search. *Recommendation*: measure search first (it exists), full SCT later if needed.
* **Q4 Bound columns and existentials.** Do Berent et al.'s results hold for Skolem existentials under
  §4 instead of wardedness? *Recommendation*: treat as research; restrict bound columns to relations
  (not constructor result positions) in the first version.
* **Q5 Reflection representation.** Names vs. locally nameless; how much of the object type system is
  visible in `Term`/`Formula` (typed reflection via indices vs untyped data + re-checking).
  *Recommendation*: untyped data + re-checking first; typed reflection later, keeping the quoted-pattern
  syntax of §6.9.
* **Q6 Directive footprints.** Are `Decl -> Decl` and `Module -> Module` enough (e.g. for directives
  that add declarations to other modules)? *Recommendation*: yes for the first version.
* **Q7 Meta-level `case` and `if`.** Only clauses at first; add `case` when needed.
* **Q8 Sealing.** Opaque ascription (`:>`) with generative abstract types. *Recommendation*: later.
* **Q9 Magic sets as an optimisation.** Optional, provably answer-preserving rewriting of programs
  *without* value invention in the transformed part. *Recommendation*: later, measured.
* **Q10 Compatibility.** Keep `%mode` as an alias of `%demand` permanently? *Recommendation*: yes.

---

## 12. Working conventions for this repository

* Development branch: `ccr-48027e29-daam41`. Work on feature branches, open PRs into it, merge when CI is
  green (squash). One theme per PR; large steps are split as in §10.
* CI equivalent (run before every push; check the **exit code**):
  `CI=1 sbt -batch clean compile Test/compile test stage scalafmtCheckAll scalafmtSbtCheck`, then
  `scripts/smoke.sh`. Format with `sbt -batch scalafmtAll` first. sbt lives in `$HOME/tools/sbt/bin`.
* Golden tests: `tests/{run,neg,pos,repl,lsp}`; regenerate with
  `HUGIN_UPDATE_CHECKS=1 sbt -batch "testOnly hugin.golden.GoldenTests"` and review every changed
  `.check`. Every error code must be in `util/ErrorCodes.scala` (a test checks the catalog against the
  emitted codes) and have a negative golden test.
* Fuzzing: `HUGIN_FUZZ_SEED=<n> HUGIN_FUZZ_COUNT=<k>` with the fuzz suites (engine vs naive evaluator,
  incremental vs from-scratch, renaming/item-order invariance).
* Scala 3 with `-Werror` under `CI=1`: no non-local `return` inside lambdas (use `boundary`).
* Diagnostics are rustc-style (`util/Diagnostics.scala`): primary label, secondary labels, notes, helps,
  suggestions with edits.
* Record semantic decisions in `docs/NOTES.md`; record design discussions and decisions in issue #1.

---

## 13. References and glossary

References (as cited during the discussion; verify details before relying on them in proofs):

* T. Gilray, A. Sahebolamri, Y. Sun, S. Kunapaneni, S. Kumar, K. Micinski. *Datalog with First-Class
  Facts.* arXiv 2411.14330 (2024/2025). DL∃!, subfact closure (§2.3), Slog (§4).
* L. Berent, M. Nissl, E. Sallinger. *Complexity of Arithmetic in Warded Datalog±.* arXiv 2202.05086
  (2022). Bound Datalog_ℤ, type-consistency (Def. 4), Algorithm 1.
* N. Stucki, A. Biboudis, M. Odersky. *A Practical Unification of Multi-stage Programming and
  Macros.* GPCE 2018 (Scala 3 quotes, splices and quoted patterns).
* M. Kaminski, B. Cuenca Grau, E. Kostylev, B. Motik, I. Horrocks. *Foundations of Declarative Data
  Analysis Using Limit Datalog Programs.* IJCAI 2017 (and JAIR version).
* A. Kovács. *Staged Compilation with Two-Level Type Theory.* ICFP 2022; elaboration-zoo (GitHub).
* D. Annenkov, P. Capriotti, N. Kraus, C. Sattler. *Two-Level Type Theory and Applications.*
* C. S. Lee, N. D. Jones, A. M. Ben-Amram. *The Size-Change Principle for Program Termination.* POPL 2001.
* R. Fagin, P. Kolaitis, R. Miller, L. Popa. *Data Exchange: Semantics and Query Answering.* (weak
  acyclicity), 2005.
* E. Rohwedder, F. Pfenning. *Mode and Termination Checking for Higher-Order Logic Programs.* ESOP 1996.
* F. Pfenning, C. Schürmann. *System Description: Twelf.* CADE 1999.
* A. Rossberg. *1ML — Core and Modules United.* (the current meta level's inspiration).

Glossary

* **Fact constructor**: a constructor whose terms are facts with Skolem identity (after the redesign: every
  constructor).
* **Value invention**: creating a value that did not exist before — a new constructor identity in a head,
  or an arithmetic result.
* **Descent / guarded induction**: the two size-change directions of §4.2.
* **Bound column**: a `min`/`max` last column of a relation that keeps only the best value per key.
* **Reify / reflect**: turning object syntax into meta data and back (§6.8).
* **Quoted pattern / hole**: a pattern in object syntax over reflective types; `$X` binds or splices
  (§6.9).
* **Footprint**: what part of a module a directive may change, read from its type (§7.1).
