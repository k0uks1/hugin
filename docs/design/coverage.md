# Coverage and unreachable clauses, independent of the split order

Design note for [issue #67](https://github.com/k0uks1/hugin/issues/67), option (b). Status: approved by
the designer. Nothing is implemented.

## 1. Recommendations

1. **Coverage is defined on probes, not on the case tree:** maximal cases at the inspected positions,
   impossibility decided by the index unifier (4.1). A clause is *reachable* if some probe matches it and
   no earlier clause (else W0006); a probe is *missing* if no clause matches it and none of its variables
   is empty (E0911 if one exists). This is Maranget's usefulness with probes for values; no split order
   enters.
2. **Each clause is elaborated once, in its own context** (right-hand side, `where`, size-change calls,
   split records), not per leaf, as in Agda, Idris 2 and Lean 4 (4.6).
3. **Missing cases are the most general missing patterns** (4.4), in a fixed order: the error shows the
   first and a count; tooling gets the full non-overlapping cover, capped at 20.
4. **A clause whose own constructors cannot occur is an error** (E0915, like Agda's
   `ImpossibleConstructor`), with a fix that removes it. Agda's absurd pattern `()` marks an empty
   position in a clause without right-hand side (`r ()`), the only new syntax (4.3).
5. **One pass in the canonical order** (stated in the reference: the leftmost decided constructor
   position of the first remaining clause; Agda's, Lean's and today's) gives the diagnostics, which do
   not depend on it, and the tree that defines evaluation. `qba` only for an optional closed-argument
   tree (Idris's runtime tree), where it is unobservable (4.7).
6. **Evaluation is the canonical tree** (Agda's "Case trees"), not a clause-matching fallback (no
   precedent). An opt-in lint `inexact_clauses`, like Agda's `--exact-split` (off by default), warns
   about clauses that do not hold definitionally.
7. **E0915 for undecided splits follows the canonical order:** the unifier postpones stuck equations
   (Agda's unifier), and a stuck split falls back to the first clause's next position (Agda's `altM1`).
8. **Reference:** `meta/coverage.md` rewritten; the canonical tree in `meta/clauses.md` "Evaluation" (7).

## 2. Hugin today

`Clauses.buildTree` splits on the first remaining clause's leftmost constructor pattern; `unifyIndices`
drops conflicting constructors and fails on a stuck equation (E0915). A node without clauses is excused
if a free variable is empty (`absurdSplit`), else missing (E0911; ≤ 20 for tooling); a clause that never
becomes a leaf is W0006. Right-hand sides, `where`, size-change calls and split records are taken **at
every leaf**; `--print-after elaborate` prints leaves. The reference defines W0006 and E0911 by the tree.

Measured on bf14ffb (scratch programs with `nat`, `bool`, `vec`, `fin`, not committed):

| # | program | result |
|---|---|---|
| t1 | `f zero zero = zero.` | E0911 ``missing: `f zero (suc _)` ``; `f (suc _) _` for tooling |
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

The tree also decides which right-hand sides type-check (r1/r2), which calls decrease (s1), what is
printed (t16) and which open terms reduce (o1/o2). Instrumenting `leaf` (scratch, reverted): the prelude
has 162 clauses and 216 leaves (15 clauses with several, up to 7); `reverse _ = []` in
`tests/run/c1_patterns.hgn` has 120 leaves, so its right-hand side is checked 120 times.

## 3. Prior art

Papers: Maranget, *Warnings for pattern matching* (JFP 2007), *Compiling pattern matching to good
decision trees* (ML 2008). Clones (`--depth 1`, in the scratchpad): agda/agda 192e0d4 (sparse:
`TypeChecking`, `doc/user-manual`), idris-lang/Idris2 1c630e6, leanprover/lean4 b8182f6 (sparse:
`Meta/Match`, `Elab/Match.lean`). Coq/Equations was not read.

### 3.1 Maranget

- Useless clauses and exhaustiveness are defined on values: row `i` is useless iff `U(P[1…i), p̄ᵢ)` is
  false, `P` is exhaustive iff `U(P, (_ … _))` is false (Definitions 4–6, Proposition 1). `Urec` (§3.1)
  specialises on the first column's constructors `Σ` (every `S(c, P)` if `Σ` is complete, else the
  default matrix `D(P)`); its result does not depend on the column order.
- Every type is assumed inhabited (§2, "non-empty type axiom"; the `t_empty` examples). `I` (§5) returns
  one witness, non-deterministically; one counter-example is argued to be enough. NP-complete, quadratic
  in practice (§7.1). Laville's lazy semantics (a clause applies if it matches and every earlier one is
  incompatible) is not sequential, hence not compilable to trees in general (§4.2).
- Trees (2008, §8.1): heuristics `f` (first row), `d`, `b` (small branching), `a` (arity), `ℓ`, `r`, and
  the necessity-based `n`, `p`, `q` (constructor prefix). The champion is `pba`; "if one wishes to avoid
  usefulness computations, we view `qba` as a good choice"; `q` is best alone (§9.2). Trees need sharing
  (§9.1). Hugin today is `f` with leftmost tie-breaking.

### 3.2 Agda

- `cover` (`Coverage.hs`, line 285) splits on the blocking variables of the first clause that is not `No`
  (`Coverage/Match.hs`, `choice`, line 185; `zipBlockingVars`, line 153), trying them in order (`altM1`,
  line 508). A strategy preferring all-constructor columns is commented out: it "fails on
  test/fail/CoverStrategy" (`splitStrategy`, 730–746).
- Unreachable clauses are those outside the used set (lines 215–228); missing clauses with an empty
  telescope become absurd clauses (`checkEmptyTel`, lines 170–176).
- Left-hand sides are checked clause by clause, trying splits in order (`Rules/LHS.hs`, lines 1029–1046);
  the unifier tries every equation (`completeStrategyAt`, `Rules/LHS/Unify.hs`, 273–285). Absurd patterns
  and clauses: 4.3.
- Evaluation is the compiled case tree built from the coverage split tree (`compileClauses`,
  `compileWithSplitTree`, `CompiledClause/Compile.hs`, lines 60–103, 132; `nextSplit`, line 189: "the
  first pattern that does a (non-lazy) match in the first clause"; `appDefE_`, `Reduce.hs`, line 981).
  Clause-by-clause reduction (`appDefE''`, lines 1027–1071) only serves while a definition has no
  compiled clauses yet (`Rules/Def.hs`, lines 402–410). The manual: "the clause `max m zero = m` does not
  hold definitionally" ("Case trees"). `--exact-split` (default off, `command-line-options.rst`, lines
  854–868) warns about such clauses (`CoverageNoExactSplit`, `Pretty/Warning.hs`, line 171) unless marked
  `{-# CATCHALL #-}`. The ESOP 2014 overlapping, order-independent clauses appear in neither manual nor
  type checker.

### 3.3 Idris 2

- Clauses are checked one by one (`checkClause`, `TTImp/ProcessDef.idr`, line 390). A clause `lhs
  impossible` must fail with a conflict (else `ValidCase`, lines 390–415); without `impossible`, a
  conflict is a unification error.
- Evaluation uses the compile-time tree: `PMDef` holds `treeCT`, `treeRT` and the checked clauses (used
  for termination) (`Core/Context/Context.idr`, lines 77–87); `evalDef` runs `treeCT`
  (`Core/Normalise/Eval.idr`, line 505). There is no clause-level reduction.
- The compile-time tree (type checking) always takes the first column; only the runtime tree uses
  Maranget's `f`, `b`, `a`, behind a flag (`nextIdxByScore`, `Core/Case/CaseBuilder.idr`, lines 744–754;
  `caseTreeHeuristics`, `Core/Options.idr`, line 199).
- Unreachable clauses and missing cases come from `treeCT` (`ProcessDef.idr`, 918–922;
  `Core/Coverage.idr`, 335), filtered by `checkImpossible`, `checkMatched` (1046–1078).

### 3.4 Lean 4

- `Meta/Match/Match.lean` splits at "the first constructor pattern in the first alternative"
  (`backward.match.rowMajor`, line 74). Empty leaves are closed by `contradiction`, failures become
  counter-examples (`processLeaf`, lines 477–495), at most 5 (`maxCounterExamples`, line 81;
  `reportMatcherResultErrors`, `Elab/Match.lean`, lines 1043–1066); unused alternatives never reach a
  leaf (`unusedAltIdxs`, line 1220).

- A `match` unfolds definitionally through its matcher (the `casesOn` tree). First-match per alternative
  holds only as conditional equation theorems whose hypotheses exclude the overlapping earlier
  alternatives, with a `splitter` for case analysis (`MatchEqs.lean`, lines 59–64, 137–222).

## 4. Assessments

### 4.1 The value space: probes

Let `f : (x₁ : A₁) → … → (xₙ : Aₙ) → B` have clauses `p̄¹ … p̄ᵐ` over its first `n` arguments. Implicit
arguments are variables. Literals are `sucᵏ zero`; quoted patterns are constructors and atoms. A
*position* is a path: an argument, then constructor arguments. `Π` is the finite set of positions at
which some clause has a constructor, literal or atom.

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
Otherwise it is *unreachable* (W0006; absurd clauses excepted, 4.3).

**Definition 2.** A probe is *missing* iff no clause matches it and it is not refuted. The clauses are
*not covering* (E0911) iff a missing probe exists.

**Assessment: these definitions go into the reference.** Definition 1 is Maranget's `U(P[1…j), p̄ʲ)` and
Definition 2 his `U(P, _̄)`, with probes for values and "not refuted" for the non-empty type axiom: a
type counts as inhabited unless every constructor of a variable conflicts. Deeper emptiness is not found:
this test is decidable, unlike inhabitation, and it is today's. Refutation only excuses missing probes: a
clause matching only refuted probes stays reachable, since `h X` (t3) is a legitimate way to write a
function on `fin zero`.

**Well-defined and decidable.** A probe is fixed by its constructors at positions of `Π`; its context is
the most general unifier of their index equations, unique up to renaming, so with all splits decided no
order matters. `Π` is finite, positions have finitely many constructors (atoms: those named plus the
rest), unification terminates, emptiness is one unification per constructor: the probes are finite and
computable (worst case exponential, as for any usefulness checker).

### 4.2 Undecided splits

A stuck split leaves the probes undefined (E0915, as today); which split is stuck can depend on the order
(t6 is stuck on `vnil` against `double n`; splitting `n` first decides everything). **Assessment: the
canonical order of 4.5 decides this error.** In every case the compiler splits the leftmost constructor
position (by argument, then depth first) of the first remaining clause whose split is decided, as Agda's
`cover` tries the first clause's blocking variables in order. E0915 if every such position is undecided,
or if a constructor pattern meets a solved term that is neither a constructor nor a variable
(`CannotMatchArgument`). The unifier postpones a stuck equation until no other makes progress (a worklist
in `unifyIndices`, like Agda's `completeStrategyAt`). When the pass succeeds every split is decided and
Definitions 1 and 2 apply. t6 stays E0915, as in Agda: its first clause inspects only the undecided
position. Refining a missing case to test refutation (4.4) skips undecided splits (the case counts as not
refuted), so an E0911 never becomes an E0915.

### 4.3 Impossible clauses and absurd patterns

**Assessment: a clause whose own constructors conflict is E0915** (t4, t3's `h fzero`): "the case for
`vcons` is impossible here: its index `suc _` conflicts with `zero`", with a machine-applicable fix that
removes the clause or, if it is the function's only clause, replaces the conflicting constructor pattern
by `()`. This is Agda's `ImpossibleConstructor`, "remove the clause, or use an absurd pattern ()"
(`Errors.hs`, 1297–1300), and Idris's unification error; E0915 ("invalid pattern") fits, so no new code.

**Absurd patterns, as in Agda.** `()` is a pattern for a position none of whose constructors can occur; a
clause containing one has no right-hand side ("if the left-hand side of a clause contains an absurd
pattern, its right-hand side must be omitted"; "the absurd pattern will only be accepted if all of these
unifications end in a conflict", `function-definitions.lagda.rst`, "Absurd patterns";
`checkAbsurdPattern` → `ensureEmptyType`, `Rules/LHS.hs`, 416–418). In Hugin:

- **Syntax** (`meta/clauses.md`): `Pattern ::= … | "(" ")"` and `Clause ::= NAME Pattern* ("=" Expr
  Where?)? "."`, the form without `=` only if some pattern contains `()`. Nested positions are allowed
  (`f (vcons X ())`). `()` is the two tokens `(` `)` with only whitespace or comments between, so the
  lexer is unchanged.
- **Today `()` means nothing:** in a pattern, an expression, a fact or a rule it is E0001 "expected an
  expression, found `)`" (measured; the reference never mentions it); `'()` is an empty quote (E0917), a
  different token. Nothing clashes: an item `f p̄.` whose patterns contain `()` is an absurd clause, any
  other `f p̄.` stays an atom.
- **Checking:** the unifier must refute every constructor at the position, in the clause's context (4.6);
  otherwise E0915 listing the possible ones (Agda's `ShouldBeEmpty`, `Errors.hs`, 434–437). An absurd
  clause with `= e` is E0915 with a fix that removes `= e` (Agda warns, `AbsurdPatternRequiresAbsentRHS`,
  `Rules/Def.hs`, 861; Hugin has no warning code for it); without `()`, an item without `=` stays an atom
  (Agda: `AbsentRHSRequiresAbsurdPattern`, `Errors.hs`, 734).
- **Coverage:** its positions join `Π`, so the probes below it are refuted and excused; it matches no
  probe, is never W0006, and makes no leaf (the tree has `Split(x, Nil)` there, as Agda's absurd clauses
  are childless nodes, `coverage-checking.lagda.rst`, 217–235). It can expose deeper emptiness; it stays
  optional where the one-level test excuses the case (t9).
- **Layout, recovery:** an absurd clause starts in column 0 like any clause, and `()` as an argument
  cannot start in column 0 (the argument rule). `parseParens` builds an `Absurd` tree at `( )` instead of
  E0001; outside clause patterns it is E0915 "an absurd pattern is only allowed in a clause's patterns".
  A missing `)` keeps today's unclosed-bracket recovery.
- **Tooling:** `()` gets the semantic token `EnumMember` (as a constructor pattern) and a TextMate rule
  `\(\s*\)` in `editors/vscode/syntaxes`; hover shows the refuted type; t13's fix writes `r ().`.

### 4.4 Presenting missing cases

Today the first missing node in tree order is shown (t1: `f zero (suc _)`). **Assessment (approved):
report `M`, the most general missing patterns.** `q ∈ M` iff (a) no clause matches a probe below `q`, (b)
some probe below `q` is missing, and (c) no generalization of `q` (a subpattern replaced by `_`)
satisfies (a) and (b). `M` is the set of prime implicants of the uncovered region: it is defined without
an order and covers every missing probe. (a) is pairwise: `q` and `p̄ʲ` clash, or their common instance
has an index conflict. `M` is sorted argument by argument, `_` first, constructors in declaration order.
The error shows the first and "and k more": t1 gives `f _ (suc _)` and `f (suc _) _`; t15 keeps `f5 _
(suc _)`; `big 3` keeps `big zero` and three more. "Add missing clauses" takes an irredundant cover in
that order (a pattern is skipped when the clauses and the patterns before it match all its missing
probes), capped at `MaxMissing` = 20. Implicit and #100's leading arguments stay hidden.

### 4.5 Algorithm: one pass

`buildTree` changes in three places:

1. **Column choice:** the canonical order (4.2); the claim below allows any, the reference fixes this one
   (4.7).
2. **Empty variables.** The tree emits `Split(x, Nil)` as today, but the analysis continues below it,
   emitting nothing, with the clauses that have no constructor there, so `h X` (t3) is marked used.
3. **Missing nodes** are refined at the positions of `Π` below them (canonical order, at most
   `MaxMissing` missing probes), and their missing probes are generalized into `M`.

**Claim: for every column choice, "clause `j` becomes a leaf" is Definition 1, and the missing probes
found are Definition 2.** Splits are at positions of `Π` and cover every possible constructor, so leaves
and missing nodes partition the probes. At a leaf, clause `j` matches every probe below, and every
earlier clause was dropped on the path because it fails there: `j` is reachable. Conversely, follow a
witness `κ` for `j` down the tree: `j` is never dropped, and no earlier remaining clause can be a leaf
(it would match `κ`), so the walk ends at a leaf for `j`. This is `U` computed along a tree (cf. Maranget
2008 §7); no run of `U` per clause is needed.

**Dependent columns.** Any free variable of a family type may be split first (`SplitProblem` solves
globally, `telescopeOrder` rebuilds telescopes), at the risk of undecided splits (4.2); a free choice is
possible but observable through evaluation (4.7).

### 4.6 Clause contexts

r1/r2, s1 and t16 depend on the leaves, an artefact of the split order. **Assessment (approved):
elaborate each clause once, in its clause context:** the single leaf of a split of that clause alone
(Cockx and Abel's left-hand side). There the right-hand side and `where` block are elaborated (`where`
functions lifted once per clause), the calls recorded against the clause's patterns, and `recordSplits`
offers the constructors possible in that context (today the last leaf wins). `--print-after elaborate`
and hover print the clauses as written. An unreachable clause whose own patterns are possible is checked
too. A leaf is `Leaf(j, σ)`, `σ` instantiating clause `j`'s context in the leaf's case (by matching).

This rejects programs: r1 type-checks and s1 terminates only through the refinement made by earlier
clauses. Both become errors, as in Agda, Idris and Lean (4.9). When a right-hand side fails in its clause
context but checks at the clause's canonical leaves, the error gets a machine-applicable fix that writes
the patterns: `w (suc N) X = X.`, `h (suc N) M = h N M.`

### 4.7 Evaluation

A tree reduces `f ū` by clause `j` only if `ū` matches `p̄ʲ` and every earlier clause clashes with it;
the converse (Laville's semantics) fails on open terms, as it is not sequential (Maranget 2007 §4.2). In
o1, `gg X (suc zero)` is determined, but the canonical tree is stuck on column 1, as Agda's tree is for
`max m zero` (3.2). So the tree is observable on open terms, and a heuristic tree would change which
programs type-check.

**Assessment: the canonical tree defines evaluation, stated in the reference** (`meta/clauses.md`
"Evaluation": the split order of 4.2; an application is stuck when a split meets a neutral). This is
Agda's and Idris's design; Lean adds clause-level first match only as theorems. The first draft's Laville
fallback has no precedent (Agda matches clause by clause only before compiling) and is dropped.

- **`inexact_clauses` (opt-in lint, a new W code):** clause `j` holds definitionally iff it is the leaf
  of exactly one node and that leaf's case is its clause context, which is Agda's test (trivial matching
  substitution, `Coverage.hs`, `cover`, lines 303–318). It flags `gg _ (suc _)` (o1) and `n2 _ _` (t16);
  off by default like `--exact-split`, so no `CATCHALL` pragma.
- **`qba` only where unobservable:** an optional second tree, used only for applications whose arguments
  are closed (detected for memoisation already), where every tree gives the first match. It is Idris's
  runtime tree with Maranget's cheap champion, and comes only if #60 measures a gain.

**Claim: the canonical tree is the only observable shape, and the reference fixes it.** W0006 and E0911
do not depend on it (4.5), clauses carry typing, termination, splits and printing (4.6), and the `qba`
tree sees only closed arguments, on which every tree gives the first match.

### 4.8 Interactions

- **Termination:** calls per clause (one set for `reverse _`, not 120); only s1-like programs lose.
- **#100:** a member's leading arguments are wildcards, never split, hidden in `M`.
- **#60:** one elaboration per clause (162, not 216, in the prelude), one pass, `M` only for E0911; the
  `qba` tree and maximal sharing (Maranget 2008 §9.1) are #60 items.

### 4.9 Conformance

| decision | precedent | citation | match |
|---|---|---|---|
| W0006/E0911 by usefulness over probes | Maranget; Agda, Idris, Lean read them off their tree | JFP §3; `Coverage.hs` 215–228; `ProcessDef.idr` 918–922; `Match.lean` 1220 | Maranget: match. Others: same verdicts as their trees when splits are decided, except emptiness (t3) |
| clause checked once in its own context | Agda, Idris, Lean | `Rules/LHS.hs` 1029–1046; `ProcessDef.idr` 416–425 | match |
| missing: first plus count, full set for tooling | Lean (≤ 5 listed), Maranget (one) | `Elab/Match.lean` 1043–1066; JFP §5 | match (cap 20) |
| impossible clause is an error | Agda `ImpossibleConstructor`; Idris unification error | `Errors.hs` 1297–1300; `ProcessDef.idr` 390–415 | match |
| absurd pattern `()`, no right-hand side | Agda absurd patterns and clauses | manual "Absurd patterns"; `Rules/LHS.hs` 416–418; `Errors.hs` 434, 734 | match; `= e` is an error, Agda warns (deviation) |
| canonical order: first clause, leftmost decided position | Agda `nextSplit`, `altM1`; Lean `rowMajor`; Idris first column | `Compile.hs` 189; `Coverage.hs` 508; `Match.lean` 74; `CaseBuilder.idr` 751 | Agda, Lean: match. Idris: column-major (deviation) |
| evaluation is the canonical tree | Agda compiled clauses; Idris `treeCT`; Lean matcher (equations only as theorems) | `Reduce.hs` 981; `Eval.idr` 505; `Match.lean` 23–56; `MatchEqs.lean` 59–64 | match |
| `inexact_clauses`, off by default | Agda `--exact-split` | `command-line-options.rst` 854–868; `Warning.hs` 171 | match; no `CATCHALL` (deviation) |
| `qba` only for closed applications | Idris runtime tree (`f`, `b`, `a`) | `CaseBuilder.idr` 744–754; ML'08 §9.2 | match in role; `qba` per Maranget |
| E0915: postponing unifier, fallback in the first clause | Agda | `Unify.hs` 273–285; `Coverage.hs` 508 | match |
| no clause-matching fallback (Laville) | none | `Reduce.hs` 1027–1071 (pre-compilation only) | dropped |
| emptiness excuses missing cases | Agda omitted absurd clauses; Lean `contradiction` | `coverage-checking.lagda.rst` 189–235; `Match.lean` 477–495 | match |

## 5. Alternatives rejected

- **Laville's rule with a clause-matching fallback** (first draft): no system does it (4.7, 4.9).
- **A heuristic tree for evaluation:** observable on open terms (o1); Idris keeps heuristics off it.
- **`U` once per clause:** same answers as the pass, `m` times the cost. **True emptiness:** undecidable.
- **Emptiness making clauses unreachable** (t3 today): flags a legitimate clause.
- **Idris's `f p̄ impossible.`:** a keyword clause form; the designer chose Agda's `()`.
- **`pba`:** the champion, but `p` needs usefulness at every node; `qba` is Maranget's choice without.

## 6. Effects

| program | today | after |
|---|---|---|
| t1 `f zero zero` | E0911 `f zero (suc _)` | E0911 `f _ (suc _)` "and 1 more" |
| t3 `h fzero. h X.` over `fin zero` | W0006 on both | E0915 on `h fzero` (fix: remove); `h X` fine |
| t4 `k zero (vcons X XS)` | W0006 | E0915 "the case for `vcons` is impossible here" (fix: remove) |
| t6 `d N vnil` first | E0915 | E0915 (as Agda) |
| r1 | accepted | E0901 with a fix `w (suc N) X = X.` |
| r2 | E0901 | E0901 (same fix) |
| s1 | accepted | E0912 with a fix `h (suc N) M = h N M.` |
| o1 | E0901 | E0901 (as Agda's `max`); `inexact_clauses` flags `gg _ (suc _)` when enabled |
| t16 `--print-after elaborate` | 3 leaves | the 2 clauses |
| unreachable clause with a type error | silent | its error |
| t13 `r fzero` over `fin zero` | W0006 | E0915, fix `r ().` |
| t5, t9, t15 | — | unchanged |

Newly rejected: right-hand sides and calls that need the refinement made by earlier clauses (r1, s1),
impossible clauses (t3, t4, t13), and type errors in unreachable clauses. Changed messages: the missing
case shown and its count. New: the opt-in `inexact_clauses` lint.

Size: about +400/−150 lines (batch 1), +350/−80 (2), +150 (3); goldens +300.

## 7. Batches

Each batch is one pull request with its reference changes.


1. **Clause contexts** (4.3, 4.6). Code: a clause's own split; impossible clauses as E0915 with the
   removal fix; absurd patterns and clauses (parser `Absurd` tree, `Clause` without right-hand side, the
   emptiness check, semantic token, TextMate grammar); right-hand side, `where` and calls once per
   clause; `Leaf(j, σ)` in `CaseTree` and `Matching`; `recordSplits` per clause; `Staging.clauses` prints
   clauses; the fix for refinement-dependent clauses. Reference: `meta/clauses.md` (new "Checking a
   clause": its context, implicit binder names, no refinement from other clauses), `meta/where.md` "Local
   definitions" ("at each leaf" → "once per clause"), `meta/termination.md` "The criterion" (the clause's
   patterns), `meta/clauses.md` "Syntax" and "Patterns" (impossible clauses, absurd patterns),
   `meta/coverage.md` (absurd clauses), `docs/errors/E0915.md`, `W0006.md`, `E0901.md`, `E0912.md`.
   Goldens: `run/cov_clause_context`, `neg/cov_refinement` (r1, s1), `neg/cov_impossible_clause` (t3, t4,
   t13), `run/cov_absurd` (`r ()`, `f (vcons X ())`), `neg/cov_absurd` (a possible `()`, `= e`, `()` in
   an expression), a recovery golden, a `print-after` golden (t16), an LSP split golden.
2. **Order-independent coverage** (4.1, 4.2, 4.4, 4.5 items 2–3). Code: the unifier's worklist, the
   canonical fallback, the analysis below empty variables, refining missing nodes, `M`, the count, the
   tooling cover. Reference: `meta/coverage.md` rewritten: "Cases and probes" (Definitions 1 and 2, the
   t3 and t9 examples), "Index unification" (postponement), "Undecided splits" (canonical order, E0915),
   "Missing cases" (`M`, order, count), "Unreachable clauses"; "Case trees" moves to `meta/clauses.md`
   "Evaluation" (batch 3); `docs/errors/E0911.md`, `W0006.md`, `E0915.md`; Maranget 2007 in
   `notation.md`. Goldens: `neg/cov_missing_general` (t1, t15, `big 3`), `run/cov_empty` (t3, t9),
   `neg/cov_undecided` (t5, t6), updated coverage goldens.
3. **Inexact clauses and the closed-application tree** (4.7). Code: the `inexact_clauses` lint; if #60
   measures a gain, a `qba` tree for closed arguments in `Matching`, with a `bench/` entry and a test
   comparing both trees on every golden. Reference: `meta/clauses.md` "Evaluation" (the canonical split
   order, stuck applications, the lint), Maranget 2008 in `notation.md`, `docs/errors/` for the new W
   code. Goldens: `run/cov_open_reduction` (o1 stuck, o2), `run/cov_inexact`.

Batch 2 needs 1, batch 3 both. Batch 1 reports how many goldens and stdlib clauses need its fix.

## 8. Sources

- Maranget, JFP 17(3) 2007 (Definitions 4–6, Prop. 1, §2, §3.1, §4.2, §5, §7.1) and ML 2008 (§7–9); Cockx
  and Abel, ICFP 2018.
- agda/agda 192e0d4: `TypeChecking/{Coverage.hs, Coverage/Match.hs, CompiledClause/Compile.hs, Reduce.hs,
  Rules/Def.hs, Rules/LHS.hs, Rules/LHS/Unify.hs, Errors.hs, Pretty/Warning.hs}`;
  `doc/user-manual/language/{function-definitions, coverage-checking}.lagda.rst`,
  `tools/command-line-options.rst`.
- idris-lang/Idris2 1c630e6: `Core/{Case/CaseBuilder, Options, Coverage, Context/Context,
  Normalise/Eval}.idr`, `TTImp/ProcessDef.idr`. leanprover/lean4 b8182f6: `Lean/Meta/Match/{Match,
  MatchEqs}.lean`, `Lean/Elab/Match.lean`.
- Hugin bf14ffb: `core/elab/{Clauses, SplitProblem, SizeChange}.scala`, `core/{CaseTree, Matching,
  Staging}.scala`, `compiler/MetaIndex.scala`, `lsp/MetaFeatures.scala`; `reference/src/meta/`.
