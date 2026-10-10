# Coverage and unreachable clauses, independent of the split order

Design note for [issue #67](https://github.com/k0uks1/hugin/issues/67), option (b). Status: proposed, for
review by the designer. Nothing is implemented.

Contents: 1 recommendations, 2 Hugin today, 3 prior art, 4 assessments, 5 alternatives rejected,
6 effects, 7 batches, 8 sources.

## 1. Recommendations

1. **Coverage is defined on probes, not on the case tree.** A *probe* is a maximal case of the
   telescope at the positions the clauses inspect, impossibility decided by the existing index unifier
   (4.1). A clause is *reachable* if some probe matches it and no earlier clause (else W0006); a probe
   is *missing* if no clause matches it and none of its variables is empty (E0911 if one exists). This
   is Maranget's usefulness with probes for values; no split order enters.
2. **Each clause is elaborated once, in its own context** (the one its own patterns produce), not per
   leaf: right-hand side, `where`, size-change calls and tooling split records. A leaf is a clause and a
   substitution. Agda, Idris 2 and Lean 4 do this; it removes the tree from typing, termination and
   printing (4.6).
3. **Missing cases are the most general missing patterns** (4.4), in a fixed order: the error shows the
   first and a count, tooling gets an irredundant cover of at most 20.
4. **A clause whose own constructors cannot occur stays W0006,** with a note naming the conflict.
   Emptiness never makes a clause unreachable; it only excuses missing probes.
5. **One splitting pass yields diagnostics and compiled tree** (4.5); any column choice gives the same
   diagnostics. The tree uses Maranget's `qba` (constructor prefix, fewest branches, smallest arity,
   leftmost).
6. **Evaluation is defined by clauses** (4.7): `f ū` reduces by clause `j` if `ū` matches `p̄ʲ` and
   every earlier clause clashes with `ū`. A tree stuck on a neutral falls back to matching clauses, so open
   terms reduce alike under every tree; closed evaluation is unchanged.
7. **E0915 for undecided splits follows a canonical order** written in the reference (leftmost decided
   position a remaining clause inspects), with a unifier that postpones stuck equations; a heuristic
   tree that meets an undecided split falls back to it.
8. **The reference gets a precise coverage chapter** (`meta/coverage.md` rewritten) and a declarative
   "Evaluation" in `meta/clauses.md`. Three batches (7).

## 2. Hugin today

`core/elab/Clauses.scala` (`buildTree`) makes a leaf when the first remaining clause has no equations
left, and otherwise splits on that clause's leftmost constructor pattern (`split`, `splitAtom`).
`unifyIndices` (`SplitProblem.scala`) drops conflicting constructors and fails at once on a stuck
equation (E0915). A node without clauses is excused if some free variable has no possible constructor
(`absurdSplit`), else it is a missing case (`missingCase`: E0911 for the first, ≤ 20 for tooling). A
clause that never becomes a leaf is W0006. `leaf` checks the right-hand side, elaborates `where`,
records the size-change calls and the tooling split records **at every leaf**, in its refined context.
`--print-after elaborate` prints the leaves (`Staging.clauses`); `Matching.runTree` is stuck on a
neutral. The reference (`meta/coverage.md`) defines W0006 and E0911 by the tree ("not the leaf of any
branch", "a branch of the case tree has no clause").

Measured on bf14ffb (scratch programs with `nat`, `bool`, `vec`, `fin`, not committed):

| # | program | result |
|---|---|---|
| t1 | `f zero zero = zero.` | E0911 ``missing: `f zero (suc _)` ``; `f (suc _) _` for tooling |
| t2 | `g _ zero = …. g zero _ = ….` | E0911 `g (suc _) (suc _)` (the split starts at column 2) |
| t3 | `h : fin zero -> nat. h fzero = …. h X = ….` | W0006 on **both** clauses (the empty split drops `h X`) |
| t3' | the same clauses swapped | no warning for `h X`, W0006 for `h fzero` |
| t4 | `k : (n : nat) -> vec bool n -> nat. k zero (vcons X XS) = …. k _ _ = ….` | W0006 on clause 1, without a reason |
| t5 | `d : (n : nat) -> vec bool (double n) -> nat. d zero vnil = …. d (suc N) (vcons X XS) = ….` | accepted |
| t6 | t5 with `d N vnil = …` first | E0915 "cannot decide whether `vnil` applies here" |
| t9 | `b : bool -> fin zero -> nat. b true X = ….` | accepted (`b false _` excused: `fin zero` is empty) |
| t15 | `f5 _ zero = …. f5 zero zero = ….` | E0911 `f5 _ (suc _)` |
| r1 | `w : (n : nat) -> sel (isz n) -> bool. w zero X = true. w N X = X.` | accepted: at its only leaf `N` is `suc _`, so `X : bool` |
| r2 | r1 with the two clauses swapped | E0901 "expected `bool`, found `sel (isz N)`" |
| s1 | `h zero _ = zero. h N M = h (predf N) M.` | accepted: at the leaf, `predf (suc k)` reduces to `k` |
| o1 | `gg zero zero = true. gg _ (suc _) = false. gg (suc _) zero = true.`, then `u X B = B` with `B : sel (gg X (suc zero))` | E0901: `gg X (suc zero)` is stuck on column 1 |
| o2 | o1 with `gg _ (suc _)` first (same function on closed values) | accepted |
| t16 | `n2 zero zero = …. n2 _ _ = ….` with `--print-after elaborate` | three printed clauses: `n2 zero (suc _)` and `n2 (suc _) _` for the second |

So the tree shows through beyond W0006 and E0911: through the leaves it decides which right-hand sides
type-check (r1/r2), which calls decrease (s1) and what is printed (t16); through evaluation, which open
terms reduce (o1/o2). Clause order acts through it even where it cannot change the function.

Instrumenting `leaf` (scratch, reverted) over the prelude, `std/`, `tests/run` and `examples`: the
prelude has 65 functions, 162 clauses, 216 leaves, 15 clauses with several leaves (up to 7); all files
(functions deduplicated by name) 262 clauses, 557 leaves. `reverse _ = []` in
`tests/run/c1_patterns.hgn` has 120 leaves: its right-hand side is checked 120 times.

## 3. Prior art

Papers: Maranget, *Warnings for pattern matching* (JFP 17(3), 2007), and *Compiling pattern matching to
good decision trees* (ML workshop 2008). Clones (`--depth 1`, in the scratchpad):
agda/agda 192e0d4 (sparse: `TypeChecking`, `doc/user-manual`), idris-lang/Idris2 1c630e6,
leanprover/lean4 b8182f6 (sparse: `Meta/Match`, `Elab/Match.lean`). Coq/Equations was not read.

### 3.1 Maranget

- Useless clauses and exhaustiveness are defined on values: row `i` is useless iff `U(P[1…i), p̄ᵢ)` is
  false, `P` is exhaustive iff `U(P, (_ … _))` is false (Definitions 4–6, Proposition 1). `Urec` (§3.1)
  specialises on the first column's constructors `Σ` (every `S(c, P)` if `Σ` is complete, else the
  default matrix `D(P)`); its result does not depend on the column order.
- Every type is assumed inhabited (§2, "non-empty type axiom"; the `t_empty` examples). `I` (§5) returns
  one witness, non-deterministically; one counter-example is argued to be enough. The problem is
  NP-complete; `m` calls of `U`, quadratic in practice (§7.1). Laville's lazy semantics (a clause applies
  if it matches and every earlier one is incompatible) is not sequential, hence not compilable to
  trees in general (§4.2).
- Trees (2008, §8.1): heuristics `f` (first row), `d`, `b` (small branching), `a` (arity), `ℓ`, `r`, and
  the necessity-based `n`, `p`, `q` (constructor prefix). The champion is `pba`; "if one wishes to avoid
  usefulness computations, we view `qba` as a good choice"; `q` is best alone (§9.2). Trees need
  maximal sharing to compete on size (§9.1). Hugin today is `f` with leftmost tie-breaking.

### 3.2 Agda

- `cover` (`Coverage.hs`, line 285) splits on the blocking variables of the first clause that is not
  `No` (`Coverage/Match.hs`, `choice`, line 185; `zipBlockingVars`, line 153), trying them in order
  (`altM1`, line 508). A strategy preferring all-constructor columns is commented out because it "fails
  on test/fail/CoverStrategy" (`splitStrategy`, lines 730–746): Agda's results depend on the order.
- Unreachable clauses are those outside the used set (lines 215–228); `CoverageNoExactSplit` warns
  about clauses that are not definitional equalities (line 239); missing clauses with an empty
  telescope become absurd clauses (`checkEmptyTel`, lines 170–176).
- Left-hand sides are checked clause by clause, trying splits in order (`Rules/LHS.hs`, lines
  1029–1046); the unifier tries every equation (`completeStrategyAt`, `Rules/LHS/Unify.hs`, 273–285).

### 3.3 Idris 2

- Clauses are checked one by one (`checkClause`, `TTImp/ProcessDef.idr`, line 390); an `impossible`
  clause must fail with a conflict (`impossibleErrOK`, lines 131–147).
- The compile-time tree (type checking) always takes the first column; only the runtime tree uses
  Maranget's `f`, `b`, `a`, behind a flag (`nextIdxByScore`, `Core/Case/CaseBuilder.idr`, lines
  744–754; `caseTreeHeuristics`, `Core/Options.idr`, line 199).
- Unreachable clauses and missing cases come from the compile-time tree (`ProcessDef.idr`, lines
  918–922; `getMissing`, `Core/Coverage.idr`, line 335); missing cases that are impossible or matched
  after all are filtered out (`checkImpossible`, `checkMatched`, `ProcessDef.idr`, lines 1046–1078).

### 3.4 Lean 4

- `Meta/Match/Match.lean` splits at "the first constructor pattern in the first alternative"
  (`backward.match.rowMajor`, line 74). Empty leaves are closed by `contradiction`, failures become
  counter-examples (`processLeaf`, lines 477–495), at most 5 (`maxCounterExamples`, line 81;
  `reportMatcherResultErrors`, `Elab/Match.lean`, lines 1043–1066); unused alternatives never reach a
  leaf (`unusedAltIdxs`, line 1220).
- Sparse splits can keep Lean from "noticing that a match statement is complete"
  (`backward.match.sparseCases`, line 65): completeness depends on how deep it splits.

### 3.5 What the references agree on

1. **Clauses are checked one by one, in their own context** (Agda, Idris, Lean); leaves select a clause.
2. **Diagnostics come off a tree split in the first clause's order** (all three), with the dependence
   documented (`CoverStrategy`, `sparseCases`). Only Maranget is order-free, and not for dependent types.
3. **Heuristics stay away from what type checking sees** (Idris: runtime tree only).
4. **Missing cases are capped** (Lean 5, Hugin 20) and filtered for impossibility (Idris, Agda).

## 4. Assessments

### 4.1 The value space: probes

Let `f : (x₁ : A₁) → … → (xₙ : Aₙ) → B` have clauses `p̄¹ … p̄ᵐ` over its first `n` arguments. Implicit
arguments are variables. A literal `k` of a nat-like type is `sucᵏ zero`. A quoted pattern is
constructor patterns of the reflective types and atoms. A *position* is a path: an argument, then
constructor arguments. `Π` is the finite set of positions at which some clause has a constructor,
literal or atom.

- A *case* is a context `Γ` and patterns `Γ ⊢ q̄ : Δ`. The first case is `x̄ : Δ`.
- *Splitting* a case at a variable `y : D ū` at a position in `Π` unifies, for every constructor `c` of
  `D`, the indices of `c`'s result type with `ū`, using the unifier of today's "Index unification".
  *Solved* `σ` gives the case `(q̄[y := c z̄])σ`, *conflict* gives no case, and *stuck* leaves the split
  *undecided*. `y` is *empty* if every constructor conflicts. A variable of an atom type splits into one
  case per atom that a clause names at that position, plus one case for every other value.
- A *probe* is a case reached by decided splits in which no variable at a position of `Π` can be split
  further: it is empty or outside `Π`. A probe is *refuted* if any of its variables is empty.
- `p̄` *matches* a probe `κ` if `κ` is an instance of `p̄`, positions solved by unification included.
  Otherwise `p̄` *fails* on `κ`: it clashes at a constructor or atom, or it has a constructor where `κ`
  has an empty variable.

**Definition 1.** Clause `j` is *reachable* iff some probe is matched by `p̄ʲ` and by no `p̄ⁱ`, `i < j`.
Otherwise it is *unreachable* (W0006).

**Definition 2.** A probe is *missing* iff no clause matches it and it is not refuted. The clauses are
*not covering* (E0911) iff a missing probe exists.

**Assessment: these definitions go into the reference.** Definition 1 is Maranget's `U(P[1…j), p̄ʲ)`
and Definition 2 his `U(P, _̄)`, with probes for values and "not refuted" for the non-empty type axiom: a
type counts as inhabited unless every constructor of a variable conflicts. Deeper emptiness is not
found: this test is decidable, unlike inhabitation, and it is today's. Refutation only excuses missing
probes: a clause matching only refuted probes stays reachable, since without absurd patterns `h X`
(t3) is how one writes a function on `fin zero`.

**Well-defined.** A probe is determined by the constructors at the positions of `Π` it reaches; its
context is the most general unifier of their index equations. The rules (deletion, solution,
injectivity, conflict, cycle) compute most general unifiers, unique up to renaming, so when every split
is decided the probes do not depend on the order of splits or equations. Matching is syntactic.

**Decidable.** `Π` is finite; a position has finitely many constructors (atoms: those named, plus the
rest); unification terminates (each step removes an equation or a variable; cycles are conflicts);
emptiness is one unification per constructor. The probes are a finite, computable set. The worst case
is exponential, as for every usefulness checker (3.1) and for today's tree.

### 4.2 Undecided splits

A stuck split leaves the probes undefined (E0915, as today), and which split is stuck can depend on the
order: t6 is stuck on `vnil` against `double n`; splitting `n` first decides everything.

**Assessment: the reference fixes a canonical order for this error only.** In every case the compiler
splits the leftmost position (by argument, then depth first) that a remaining clause inspects and whose
split is decided. E0915 if every such position is undecided, or if a constructor pattern meets a solved
term that is neither a constructor nor a variable (`CannotMatchArgument`). The unifier postpones a stuck
equation until no other makes progress (a worklist in `unifyIndices`, like Agda's
`completeStrategyAt`). If the heuristic tree (4.5) meets an undecided split, the function is compiled
again in the canonical order; when that succeeds every split is decided and Definitions 1 and 2 apply.
t6 is accepted. Refining a missing case to test refutation (4.4) skips undecided splits (the case counts
as not refuted), so an E0911 never becomes an E0915.

### 4.3 Impossible clauses

**Assessment: W0006, with a reason.** A clause whose own constructors conflict (t4, t13) matches no
probe. The note names the constructor and the conflicting index (`vcons` needs `suc _`, the argument is
`zero`). Agda rejects such clauses and Idris requires `impossible`; Hugin keeps a warning, since the
program is not wrong, and `fix` removes the clause.

### 4.4 Presenting missing cases

Today the first missing node in tree order is shown (t1: `f zero (suc _)`; column 1 first would give
`f _ (suc _)`); Maranget's `I` returns any one witness.

**Assessment: report `M`, the most general missing patterns.** `q ∈ M` iff (a) no clause matches a
probe below `q`, (b) some probe below `q` is missing, and (c) no generalization of `q` (a subpattern
replaced by `_`) satisfies (a) and (b). `M` is the set of prime implicants of the uncovered region: it is
defined without an order and covers every missing probe. (a) is pairwise: `q` and `p̄ʲ` clash, or their
common instance has an index conflict. `M` is sorted argument by argument, `_` first, constructors in
declaration order. The error shows the first and "and k more": t1 gives `f _ (suc _)` and `f (suc _)
_`; t15 keeps `f5 _ (suc _)`; `big 3` keeps `big zero` and three more. "Add missing clauses" takes an
irredundant cover in that order (a pattern is skipped when the clauses and the patterns before it match
all its missing probes), capped at `MaxMissing` = 20. Implicit and #100's leading arguments stay hidden.

### 4.5 Algorithm: one pass

`buildTree` changes in three places:

1. **Column choice.** Any position a remaining clause inspects may be split. The tree ranks candidates
   by `qba`: the number of remaining clauses, from the first, with a constructor there; then fewer
   possible constructors (counted with `canApply`'s fast path); then the smaller sum of arities; then the
   leftmost. It takes the first decided one.
2. **Empty variables.** The tree emits `Split(x, Nil)` as today, but the analysis continues below it,
   emitting nothing, with the clauses that have no constructor there, so `h X` (t3) is marked used.
3. **Missing nodes** are refined at the positions of `Π` below them (canonical order, at most
   `MaxMissing` missing probes), and their missing probes are generalized into `M`.

**Claim: for every column choice, "clause `j` becomes a leaf" is Definition 1, and the missing probes
found are Definition 2.** Splits are at positions of `Π` and cover every possible constructor, so leaves
and missing nodes partition the probes. At a leaf, clause `j` matches every probe below, and every
earlier clause was dropped on the path because it fails there: `j` is reachable. Conversely, follow a
witness `κ` for `j` down the tree: `j` is never dropped, and no earlier remaining clause can be a leaf
(it would match `κ`), so the walk ends at a leaf for `j`. This is `U` computed by specialization along a
tree (Maranget 2008 §7 relates necessity and usefulness the same way); no run of `U` per clause is
needed.

**Dependent columns.** A position may be split once its variable is free and its type is a family
application: Cockx and Abel's split rule needs no telescope order, because the `SplitProblem` solves
variables globally and `telescopeOrder` rebuilds a telescope at each leaf. A column whose type mentions
earlier columns can go first; its unification may solve them (`vec bool n` solves `n`), and a solved
column needs no split. The only cost of the free choice is undecided splits (4.2).

### 4.6 Clause contexts

r1/r2, s1 and t16 depend on the leaves, and a heuristic tree has other leaves. **Assessment: elaborate
each clause once, in its clause context:** the single leaf of a split of that clause alone (Cockx and
Abel's left-hand side). There the right-hand side and `where` block are elaborated (`where` functions
lifted once per clause), the calls recorded against the clause's patterns, and `recordSplits` offers the
constructors possible in that context (today the last leaf wins). `--print-after elaborate` and hover
print the clauses as written. An unreachable clause whose own patterns are possible is checked too. A
leaf is `Leaf(j, σ)`, `σ` instantiating clause `j`'s context in the leaf's case (by matching).

This rejects programs: r1 type-checks and s1 terminates only through the refinement made by earlier
clauses. Both become errors, as in Agda, Idris and Lean (3.5). When a right-hand side fails in its
clause context but checks at the clause's canonical leaves, the error gets a machine-applicable fix that
writes the patterns: `w (suc N) X = X.`, `h (suc N) M = h N M.`

### 4.7 Evaluation

A tree reduces `f ū` by clause `j` only if `ū` matches `p̄ʲ` and every earlier clause clashes with `ū`
(the path follows `ū`'s constructors; index solutions are forced by `ū`'s type). The converse fails for
open terms: "matches, and every earlier clause is incompatible" is Laville's semantics, which is not
sequential, so no tree implements it in general (Maranget 2007 §4.2). In o1, `gg X (suc zero)` is
determined (clause 1 clashes at column 2, clause 2 matches), yet today's tree is stuck on column 1, and a
`qba` tree is not: switching heuristics alone would change which programs type-check.

**Assessment: evaluation is Laville's rule, implemented as the tree plus a fallback.** `f ū` reduces to
clause `j`'s right-hand side if `ū` matches `p̄ʲ` and every earlier clause clashes with it (different
constructors or atoms at some position); otherwise it is neutral. When `runTree` is stuck on a neutral
at a flagged node, the clauses are matched one by one. A node is flagged unless its first remaining
clause has a constructor at the split position and at no other unsplit position: only then is the
tree's answer final. Closed arguments never get stuck, so closed evaluation and memoisation are
unchanged; open terms reduce at least as often as today, identically under every tree. o1 is accepted.

**Claim: no tree shape changes a diagnostic or a value.** W0006 and E0911 follow Definitions 1 and 2
(4.5), E0915 the canonical order (4.2); typing, termination, split records and printing work on clauses
(4.6); evaluation follows Laville's rule (4.7). First-match semantics is kept: on closed arguments every
tree selects the first matching clause, and `Leaf(j, σ)` evaluates that clause's right-hand side.

### 4.8 Interactions

- **Size-change termination:** calls per clause (4.6): `reverse _` adds one set of calls instead of 120.
  A clause's matrix is its leaves' matrix without their refinement; only s1-like programs lose.
- **#100 member functions:** leading arguments are wildcards, never split, never `qba` candidates,
  hidden in `M`.
- **Performance (#60):** one elaboration per clause (162 instead of 216 in the prelude), one pass as
  today, `M` only on the E0911 path, the fallback only on stuck applications at flagged nodes. Maximal
  sharing (Maranget 2008 §9.1) is a later #60 item.
- **Incrementality:** none; a clause group stays one block.

## 5. Alternatives rejected

- **(a) Left-to-right tree for diagnostics, heuristics for the compiled one:** the designer chose (b);
  leaves and open evaluation would still differ between the trees (4.6, 4.7).
- **Idris's two trees** (3.3): doubles compilation, keeps an order in the language, and the heuristic
  tree's leaves would need bodies typed at other leaves.
- **`U` once per clause:** the same answers as the pass (4.5) at `m` times the cost.
- **True emptiness:** undecidable; one level is today's test and Agda's (`checkEmptyTel`).
- **Emptiness making clauses unreachable** (t3 today): flags the only possible clause of an empty type.
- **One arbitrary witness, as `I`:** the first of `M` is defined, and `M` feeds tooling.
- **Clause context = least general generalization of the clause's reachable probes:** keeps r1 and s1
  order-free, but has no prior art and needs extra one-branch splits so that each leaf is an instance
  of it. Open, if the designer prefers it to 4.6's fix.
- **Impossible clauses as errors** (Agda): breaks programs that compile today, for no soundness gain.
- **`pba`:** the champion, but `p` needs usefulness at every node; `qba` is Maranget's choice without.

## 6. Effects

| program | today | after |
|---|---|---|
| t1 `f zero zero` | E0911 `f zero (suc _)` | E0911 `f _ (suc _)` "and 1 more" |
| t3 `h fzero. h X.` over `fin zero` | W0006 on both | W0006 on `h fzero`, with the conflict |
| t4 `k zero (vcons X XS)` | W0006 | W0006 with "`vcons` needs `suc _`, the argument is `zero`" |
| t6 `d N vnil` first | E0915 | accepted |
| r1 | accepted | E0901 with a fix `w (suc N) X = X.` |
| r2 | E0901 | E0901 (same fix) |
| s1 | accepted | E0912 with a fix `h (suc N) M = h N M.` |
| o1 | E0901 | accepted |
| t16 `--print-after elaborate` | 3 leaves | the 2 clauses |
| unreachable clause with a type error | silent | its error |
| t13 `r fzero` over `fin zero` | W0006 | W0006 with the conflict |
| t2, t5, t9, t10–t12, t14, t15 | — | unchanged |

Newly accepted: t6-like and o1-like programs. Newly rejected: right-hand sides and recursive calls that
need the refinement made by earlier clauses (r1, s1), and type errors in unreachable clauses. Changed
messages: the missing case shown, its count, the reason for W0006.

Size: batch 1 about +300/−150 lines of Scala, batch 2 about +350/−80, batch 3 about +200/−40; goldens
about +250.

## 7. Batches

Each batch is one pull request and changes the reference with the code (CONTRIBUTING.md, "Changing the
language").

1. **Clause contexts** (4.3, 4.6). Code: a clause's own split with the conflict note; right-hand side,
   `where` and calls once per clause; `Leaf(j, σ)` in `CaseTree` and `Matching`; `recordSplits` per
   clause; `Staging.clauses` prints clauses; the fix for refinement-dependent clauses. Reference:
   `meta/clauses.md` (new "Checking a clause": its context, implicit binder names, no refinement from
   other clauses), `meta/where.md` "Local definitions" ("at each leaf" → "once per clause"),
   `meta/termination.md` "The criterion" (the clause's patterns), `meta/coverage.md` "Unreachable
   clauses" (impossible constructors), `docs/errors/W0006.md`, `E0901.md`, `E0912.md`. Goldens:
   `run/cov_clause_context`, `neg/cov_refinement` (r1, s1 with the fix), `neg/cov_impossible_clause`
   (t4), a `print-after` golden (t16), an LSP split golden.
2. **Order-independent coverage** (4.1, 4.2, 4.4, 4.5 items 2–3). Code: the unifier's worklist, the
   canonical fallback, the analysis below empty variables, refining missing nodes, `M`, the count, the
   tooling cover. Reference: `meta/coverage.md` rewritten: "Cases and probes" (Definitions 1 and 2, the
   t3 and t9 examples), "Index unification" (postponement), "Undecided splits" (canonical order,
   E0915), "Missing cases" (`M`, order, count), "Unreachable clauses"; "Case trees" goes;
   `docs/errors/E0911.md`, `W0006.md`, `E0915.md`; Maranget 2007 in `notation.md`. Goldens:
   `neg/cov_missing_general` (t1, t15, `big 3`), `run/cov_empty` (t3, t9), `run/cov_undecided_order`
   (t6), updated coverage goldens.
3. **Heuristic trees, evaluation by clauses** (4.5 item 1, 4.7). Code: `qba` in `buildTree`, flagged
   nodes and the clause fallback in `Matching`, a `bench/` entry for tree size and evaluation (#60).
   Reference: `meta/clauses.md` "Evaluation" (Laville's rule replaces "evaluates its case tree"),
   `meta/coverage.md` (the tree is not observable), Maranget 2008 in `notation.md`. Goldens:
   `run/cov_open_reduction` (o1, o2); a test compiling every golden's functions in both orders and
   comparing diagnostics and closed results, like `Clauses.crossCheck`.

Batch 2 needs batch 1 (checking must leave the leaves before the pass may take another path); batch 3
needs both. Batch 1 is the riskiest: its pull request reports how many goldens and stdlib clauses need
its fix.

## 8. Sources

- L. Maranget, *Warnings for pattern matching*, JFP 17(3), 2007: Definitions 4–6, Proposition 1, §2,
  §3.1, §4.2, §5, §7.1. *Compiling pattern matching to good decision trees*, ML 2008: §7, §8.1, §9.1–9.2.
  J. Cockx, A. Abel, *Elaborating dependent (co)pattern matching*, ICFP 2018.
- agda/agda 192e0d4: `TypeChecking/Coverage.hs`, `Coverage/Match.hs`, `Rules/LHS.hs`,
  `Rules/LHS/Unify.hs`.
- idris-lang/Idris2 1c630e6: `Core/Case/CaseBuilder.idr`, `Core/Options.idr`, `Core/Coverage.idr`,
  `TTImp/ProcessDef.idr`.
- leanprover/lean4 b8182f6: `Lean/Meta/Match/Match.lean`, `Lean/Elab/Match.lean`.
- Hugin bf14ffb: `core/elab/Clauses.scala`, `SplitProblem.scala`, `SizeChange.scala`,
  `core/CaseTree.scala`, `core/Matching.scala`, `core/Staging.scala`, `compiler/MetaIndex.scala`,
  `lsp/MetaFeatures.scala`; `reference/src/meta/coverage.md`, `clauses.md`, `where.md`,
  `termination.md`.
