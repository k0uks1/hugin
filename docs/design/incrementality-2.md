# Incremental compilation, second round

Design note for [issue #126](https://github.com/k0uks1/hugin/issues/126): what established incremental
compilers do that Hugin does not, measured against Hugin's own latency on realistic edits. Status:
proposed, for review by the designer. Nothing is implemented.

Contents: 1 recommendations, 2 what we have, 3 measurements, 4 prior art and fit, 5 alternatives
rejected, 6 ranked pull requests, 7 interactions with #91 and #100, 8 sources.

## 1. Recommendations

1. **Fix what the measurements show before adopting machinery.** Three of the four largest costs of an
   edit are not missing techniques but places where our own per-item design leaks: an item with a syntax
   error is filed with the declarations, so most keystrokes inside a rule elaborate the whole file again
   (3.3); revalidating the items of a 4 850-line file is quadratic (3.4); and the whole-program tail
   after elaboration (module-wide expansion, staging, the object phases) is now most of an edit (3.2).
2. **Adopt rustc's projection-query pattern ("firewalls") in four places**, each with a comparable
   summary in front of a result that has no useful equality: erroneous items in front of the
   declarations (PR 1), the lowered rules in front of evaluation (PR 3), and, later, the fingerprints of
   the declarations and of a library's exports in front of the items (PR 7).
3. **Adopt cancellation in the language server** (salsa, rust-analyzer, Lean): a new edit stops the work
   for the old text instead of queueing behind it (PR 5).
4. **Reuse the evaluated fixpoint in the REPL** (PR 3, then per component, PR 4) instead of an
   incremental Datalog algorithm: the inputs (facts files) rarely change, the program grows.
5. **Do not adopt now:** durability (measured: under 0.3 % of an edit), incremental reparsing (7 % on
   the largest file, and the slice check already makes reuse exact), LRU of memo values, parallel
   queries, DRed, counting and differential dataflow (section 5).

## 2. What we have

`docs/INCREMENTALITY.md` describes the database and steps 0 to 10. Since the redesign (B3c) the program's
elaboration is: `ItemSlices` (whole parse, then each item from its own slice), `DeclarationsOf` (cut off
by item fingerprints), `Signatures` (all declarations, definitions, clauses and formula functions of the
file together, in a fork of the library chain's core), `ElabItem` per object item (rule, query,
directive; a fork of the declarations' core), `ElabProgram` (`ProgramElab.assemble`: items moved into one
fork, non-portable items elaborated again, module-wide directives and `%demand` expanded), then the
phases of `Compiler.phasePlan` (stage, directives, constant folding, moding, records and disjunctions,
derivations, stratification, bound columns, completeness, termination, lowering), all inside `Compile`.

The database (`query/Database.scala`, 296 lines) has red-green revalidation, early cut-off, accumulators,
`onCycle` fallbacks and reachability-based eviction. Two facts the Status section does not reflect:

- `ElabItem` depends on the whole `Signatures` value, which has no equality: editing or adding any
  declaration elaborates every object item (`ItemQueriesSuite`, "editing a declaration elaborates the
  declarations and every object item again"). Step 10's `ScopeName`/`DeclAfter` dependencies were not
  ported to the redesigned meta level (`INCREMENTALITY.md`, header note); the Status section still
  describes them.
- No query pushes to an accumulator any more; `FileDiagnostics.of` groups `Compile`'s diagnostics by
  file. The mechanism is tested (`DatabaseAccumulatorSuite`) but unused.

Keys: an object item is `ItemKey(path, tree, occurrence)`, salsa's identity hash plus disambiguator
(4.1). Libraries are a chain of forks (`ElabLibrary`); the standard library is shared per process
(`StdlibCache`). The language server answers on lsp4j's message thread, one change at a time, and
publishes every open document after each change. The REPL's queries are extra items of the session's
program; each one evaluates the program from scratch (`Evaluate`).

## 3. Measurements

Built at 348fd8e. Throwaway instrumentation in the scratchpad (not committed): a driver that sets
`SourceText` like an editor and demands the queries in pipeline order, timing each step as the work it
adds beyond the previous ones (main-thread CPU time, `ThreadMXBean`, as `Bench cpu`), with the
database's execution counts; phase times from `Context.timings`; `Features` for the language server;
`Session` for the REPL; async-profiler on loops of one edit. Medians of 5 to 9 repetitions after warm-up,
in one JVM; 4 vCPU container shared with other builds, so differences under ~15 % are noise. Every edit
uses fresh text per repetition (an undo would hit old memos). `split` is `bench/gen/large.hgn` cut in two
at group 75: a 2 417-line program with `%use` of a 2 435-line library.

### 3.1 Latency per edit (ms)

| program | lines | from scratch | edit a rule | type in a rule | edit a decl | add a decl |
|---|---:|---:|---:|---:|---:|---:|
| `examples/typechecker` (`%demand`) | 25 | 63 | 26 | 14 | 30 | 21 |
| `tests/run/a04_typechecker` (`%demand`) | 25 | 16 | 14 | 10 | 17 | 19 |
| `tests/run/c2_module_wide` | 27 | 27 | 7.7 | 4.3 | 13 | 11 |
| `bench/meta/meta_scaled` | 249 | 682 | 609 | — | 546 | 622 |
| `bench/gen/large` | 4 850 | 1 190 | 445 | 467 | 869 | 927 |
| `split`, edit in the program / library | 2 417 + 2 435 | 720 | 330 / 623 | — | — / 673 | — |

"Type in a rule" inserts `_tmp` after a variable one character at a time (every state is valid).
`f_modules`' rules are clauses of formula functions, so they are declarations (13 ms, `Signatures` 6).

Language server, per change (`didChange` with publication, then semantic tokens, inlay hints, code
lenses, document symbols): typechecker 20 ms (rule) and 20 ms (declaration); `large` 493 ms (rule; 459
publishing, 23 tokens, 9 code lenses) and 935 ms (declaration). The follow-up requests are cheap; the
compile is the latency.

### 3.2 Where an edit goes

| step | typechecker, rule | meta_scaled, rule | large, rule | large, decl |
|---|---:|---:|---:|---:|
| whole parse and slices | 1.3 | 2.8 | 32 (7 %) | 34 |
| items, import graph, `StdChain` | 0.8 | 1.9 | 27 (6 %) | 30 |
| `Signatures` | 0 | 0 | 0 | 21 |
| `ElabItem` (executed / revalidated) | 1.6 (1) | 1.9 (1) | 114 (1 of 3 691; 26 %) | 448 (3 691) |
| `ElabFile` (assemble, expansion) | 12.3 (47 %) | 569 (93 %) | 40 (9 %) | 51 |
| stage and object phases | 9.6 (37 %) | 33 | 232 (52 %) | 233 |

`large`'s object phases: stage 67, termination 49, records and disjunctions 39, stratification 20,
lowering 17, completeness 12, moding 7. The profile of a `large` rule-edit loop: `ItemOf` 20 % of the
main thread (each of 3 691 `ItemOf` scans `ObjectItems` with `==` on whole trees; `ItemKey.equals` 8 %);
`DepGraph.edges` built three times (stratification, completeness, termination; 7 % together). The
profile of a `meta_scaled` rule-edit loop: `expandModule` 76 % (`Matching.reduceFunction` 63 %, read-back
20 %). `INCREMENTALITY.md` calls the object phases "cheap next to elaboration"; that was true before
per-item elaboration, not after it.

### 3.3 Typing with parse errors

Typing a copy of a rule after itself, every third character: `Items.splitItems` (line 41) files every item
with a syntax error among the declarations (so that the names it might declare are not reported as
unresolved), so `DeclarationsOf` changes and `Signatures` and every item run again. In typechecker 21 of
28 keystrokes elaborate all declarations and items (21 ms median against 13); in `large` 9 of 21 (each
like a declaration edit, ~870 ms against ~450).

### 3.4 Revalidation, durability, memory

After a change to an unrelated input, `Compile` revalidates without executing anything: `large` 12 252
memos in 6.5 ms (0.5 µs per memo); the small programs 54 to 74 memos in 0.01 to 0.03 ms. The library
part: the prelude chain is 33 to 44 memos; a library file is parsed and elaborated as one, so it is a
handful of memos (`split`'s chain revalidates in 0.33 ms with the program's own parse included). What
durability skips is therefore under 0.05 ms per edit on small programs and under 1 ms (0.3 %) on `large`.
The cost of revalidation is the number of items, not the libraries; PR 2 removes the quadratic part.

### 3.5 The REPL

| session | compile after a query | query (median) | load facts |
|---|---:|---:|---:|
| `bench/datalog/tc` (179 700 tuples) | 2.4 | 322 to 432 | 318 |
| `bench/datalog/strata` | 3.2 | 234 to 245 | 231 |

Every query evaluates from scratch (and parses the facts file again), although the rules did not change.

## 4. Prior art and fit

Clones (`--depth 1`, sparse where large, in the scratchpad): salsa-rs/salsa 30b614d,
rust-lang/rustc-dev-guide 20a4fdd, rust-lang/rust-analyzer 88552f8, leanprover/lean4 b8182f6,
dotnet/roslyn 7ac1c03, sbt/zinc 5256804, TimelyDataflow/differential-dataflow aa8745f.

### 4.1 salsa

- **The core is small.** Revalidation is `deep_verify_edges` (`function/maybe_changed_after.rs` 580–647):
  walk the recorded edges in execution order, stop at the first changed one (the comment at 592–597 says
  why order matters), as our `Database.fresh` does with `forall`. Backdating is
  `backdate_if_appropriate` (`function/backdate.rs` 15–58), our early cut-off. Of salsa's 20 700 lines,
  the bulk is elsewhere: fixpoint cycles (`cycle.rs` 525 lines, most of `maybe_changed_after.rs` and
  `execute.rs`), concurrency (`function/sync.rs` 621, `sync.rs`, `runtime.rs`), and identity (`interned.rs`
  1 965, `tracked_struct.rs` 1 520, `table.rs`, `zalsa_local.rs` 2 527). Our 296 lines are the core
  without those three.
- **Durability**: inputs carry a level; a write records the revision per level (`runtime.rs` 224–238);
  a memo whose inputs all have a higher durability than any input changed since it was verified is valid
  without walking (`maybe_changed_after.rs` 371–389). rust-analyzer gives library files `HIGH`
  (`base-db/src/change.rs` 93–99). Fit: easy (a level per `SourceText`, `<stdlib>` and files not open
  `HIGH`). Gain: 3.4, under 0.3 %. Not now; it becomes worth it only if libraries are split into items.
- **Tracked structs**: entities created inside a query, identified by an identity hash of their id
  fields plus a disambiguator counting equal hashes in the same query (`tracked_struct.rs` 214–242,
  reuse 307). Fit: `ItemKey(path, tree, occurrence)` is exactly this. Nothing to adopt.
- **Interning**: values replaced by small ids that never change (`interned.rs` 394). Fit: the memo keys
  `ItemQueryKey` hash and compare whole item trees on every lookup (3.2). A cached hash and an index
  (PR 2) give most of the benefit without a global intern table.
- **LRU**: evicts a memo's *value* but keeps its edges, so dependents still verify
  (`function.rs` 505–512, `function/memo.rs` 90–97). Fit: our `collect` drops unreachable memos whole,
  which is what an editor's memory needs; value-only eviction would matter for large values kept
  reachable, which we have not seen. Not now.
- **Cancellation**: a pending write sets a flag and blocks until other handles finish (`storage.rs`
  150–175); every query invocation checks it and unwinds (`database.rs` 115, `cancelled.rs`).
  rust-analyzer calls it on every change (`ide-db/src/apply_change.rs` 14). Fit: our queries are pure and
  `execute` stores no memo when `compute` throws, so unwinding is safe; the slices' placement is set by
  `ItemSlices` under the same lock. PR 5.
- **Parallel queries**: the reason for most of salsa's concurrency code. Fit: per-item elaboration forks
  a shared core, so items could run in parallel on a cold start (`large`: 741 ms of `ElabItem`), but an
  edit elaborates one item. Not now.

### 4.2 rustc

- **Red-green** (`queries/incremental-compilation-in-detail.md` 94–191, `try_mark_green`) is our
  algorithm; **fingerprints** (267–290) make results comparable across sessions, which we do not need
  in-process (equality suffices; no on-disk cache, designer decision).
- **`eval_always` and `no_hash`** (432–480) and the **projection query pattern** (497–539): a monolithic
  result that always changes, with small per-item projections whose equality shields the dependents.
  Fit: `Signatures`, `ElabBase` and `Compile` are such monoliths. `DeclarationsOf` is already a
  projection of the parse; PR 1 corrects what it projects, PR 3 adds one in front of evaluation, PR 7 one
  per declaration and per library export.

### 4.3 rust-analyzer

- **Incremental reparsing** (`syntax/src/parsing/reparsing.rs` 1–7): relex one token, or reparse the
  innermost `{}` block, only if its tokens are balanced (108, 144). Fit: Hugin's analogue is the slice:
  each item is parsed from its own text and kept by text (`ParseItem`); only the whole-file parse that
  finds the boundaries remains (7 % on `large`). Not now.
- **Item trees as the firewall** (`hir-def/src/item_tree.rs` 1–15): a per-file summary of items without
  bodies; "when typing inside an item body, the `ItemTree` of the modified file is typically
  unaffected". Fit: `DeclarationsOf` plays this role, but files broken items with the declarations (3.3).
  PR 1 makes the summary of a broken item what the declarations read of it.
- **`DefMap` per crate and per block** (`hir-def/src/nameres.rs` 1–30): name resolution as a query of
  its own. Fit: our scope is part of `Signatures`; PR 7 needs the per-name lookups as dependencies.

### 4.4 Lean 4

`Language/Lean.lean`: after each command the whole state is a snapshot; a new version reuses every
command whose syntax is unchanged and that starts before the edit (note at 80–110; `parseCmd` 558–625:
the "unchanged" path 563–585, the fast path via `isBeforeEditPos` 271 and 590), and on the first changed
command cancels all later snapshots (`cancelRec`, 619–624) and re-elaborates them. The header (imports)
is processed once. Fit: Lean's reuse is a *prefix* rule because its commands are elaborated in order;
Hugin's items are order-independent and already reused individually, so the prefix rule is weaker than
what we have, except for the declarations, which are elaborated together. After #91 the declarations
are elaborated by components in topological order; a chain of per-component queries would give Lean's
prefix reuse inside `Signatures` (PR 9). Lean's per-snapshot cancellation tokens are PR 5's model for
the language server.

### 4.5 Roslyn

Green nodes are position-free and parent-free, red nodes add positions lazily ("Red-Green Trees.md");
the incremental parser reuses old tokens and whole nodes at list boundaries outside the changed range
("Incremental Parser.md" 176–236), never a node with diagnostics (`Blender.Reader.cs` `CanReuse`,
215–242). The declaration table merges per-file declaration summaries, cached for the pattern "one file
edited, the rest constant" (`DeclarationTable.cs` 15–22). Fit: item slices are our green nodes and
`SourceFile.place` our red layer (step 9), and like Roslyn we do not reuse a slice with parse errors
(`Slices.congruent`). The declaration-table idea is what PR 7 does for declarations within a file.

### 4.6 zinc and Kotlin

zinc hashes each simple name's definitions in a class's extracted API (`NameHashing.scala` 29–38) and
invalidates dependents only if a name they use changed its hash (`IncrementalNameHashing.scala` 71,
`findAPIChange`); Kotlin's incremental compilation does the same with ABI snapshots. Fit: per-file
invalidation across compiler runs is out of scope (no serialization), but the *idea* applies within a
process: an item, or a program importing a library, depends on the names it uses and their
fingerprints, not on the whole providing module (PR 7).

### 4.7 Adapton and self-adjusting computation

Adapton (Hammer et al., PLDI 2014) builds a demanded computation graph, dirties eagerly and repairs
lazily on demand; salsa and our database verify lazily from the demanded root, which is the same
consistency for pure queries. Nominal Adapton (Hammer et al., OOPSLA 2015) names allocations so that
reuse survives structural change, our `ItemKey`. Self-adjusting computation (Acar's thesis, CMU 2005;
Acar et al., TOPLAS 2009) memoises function calls in a trace and reuses a recursive call on an unchanged
suffix (the list-map example). Fit: the module-wide expansion (76 % of a `meta_scaled` edit) is a
meta-level traversal of the module; reusing its calls on unchanged parts across revisions is the
remaining large gain, and the hardest (PR 8).

### 4.8 Incremental Datalog maintenance

- **Counting and DRed** (Gupta, Mumick, Subrahmanian, SIGMOD 1993): counting keeps derivation counts
  (non-recursive views), DRed over-deletes and re-derives for recursive ones; insertions are a
  continuation of semi-naive evaluation.
- **Differential dataflow** (McSherry et al., CIDR 2013; `differential-dataflow/src/operators/iterate.rs`
  1–12) and **DDlog** (Ryzhyk and Budiu, Datalog 2.0 2019): collections of timestamped differences;
  iteration circulates differences to a fixpoint, so any input change is maintained.
- Fit: the REPL's changes are *new rules and queries* over facts that rarely change (3.5), and with
  `%demand` a query changes the program itself. Stratified negation and aggregates make deletion
  non-monotone (DRed's re-derivation per stratum; counting does not cover recursion), and first-class
  facts and bound columns (`min`) make derivation counts unsound to keep without care. Differential
  dataflow would replace the engine (`runtime/Engine.scala`) and its memory profile. The measured need is
  met by reusing what did not change: the whole fixpoint when the lowered rules are equal (PR 3), else
  each component whose rules and inputs are unchanged, continuing semi-naive evaluation when a
  component only gained rules (PR 4).

## 5. Alternatives rejected

- **Durability now**: under 0.3 % of an edit (3.4); revisit if libraries get per-item elaboration.
- **Incremental reparsing of the file** (rust-analyzer, Roslyn): 7 % of a `large` edit, and the slice
  check must still compare the result with a whole parse to keep error recovery identical.
- **LRU of memo values**: our reachability eviction bounds memory by what is asked (`ItemQueriesSuite`,
  500 random edits); no large reachable value has shown up.
- **Parallel queries**: helps cold starts, not edits; costs thread-safety of `Core` caches.
- **DRed, counting, differential dataflow**: 4.8.
- **Lean's prefix rule for items**: weaker than per-item reuse (4.4); kept only for components (PR 9).
- **On-disk caches** (rustc, zinc, `.olean`): designer decision in #60.

## 6. Ranked pull requests

Each is one pull request, keeps `IncrementalSuite`, `ItemQueriesSuite` (including the random-edit and
memory tests), `LibraryQueriesSuite` and `DatabaseSuite` green, and adds execution-count tests for its
claim. Measurement plan for all: the scratch driver of 3 (to be added as a `Bench edits` mode of
`src/test/scala/hugin/bench/Bench.scala` in PR 2, so later PRs report against it), main-thread CPU in
alternating JVMs as `Bench cpu`.

1. **Broken items are summarised for the declarations.** `DeclarationsOf` carries, for an object item
   with a syntax error, only what `elabDeclarations` reads of it: the names it might declare
   (`mightDeclare`) and the function whose clause it is, if any (`state.erroneous`,
   `state.unelaborated`, `Items.scala` 64–67); a declaration with a syntax error stays as it is. Expected:
   75 % of keystrokes in typechecker from 21 to ~13 ms, 43 % of keystrokes in `large` from ~870 to ~450
   ms. Test: typing a rule character by character elaborates `Signatures` only when the summary changes
   (counts), and equals from scratch at every step. Risk: low; the summary must cover every read
   (audit `Items.scala`: `drop` 168–171, the lookup at 277).
2. **Linear revalidation of items.** `ObjectItems` indexed by key, `ItemKey` with a cached hash (the
   identity of 4.1 without an intern table), and the Status section of `INCREMENTALITY.md` corrected
   (2). Expected: `large` rule edit −20 % (~−100 ms); no change on small files. Test: the existing counts;
   a 5 000-item program revalidates in linear time (a bound on `ItemOf` executions per edit).
3. **The REPL reuses the fixpoint.** `Evaluate` split into a projection of the lowered program without
   its queries (rules, relation layout, directives: comparable values) and the facts' texts, a
   `Fixpoint` query on it holding the engine, and the answers of the queries against it; facts files
   parsed once per text. Expected: a `tc` query from ~320 ms to under 10 ms, `strata` from ~240 ms;
   loading facts unchanged. A query on a `%demand` relation changes the program and evaluates again
   (PR 4). Test: `SessionSuite` counts of `Fixpoint` executions; answers equal from scratch.
4. **Per-component evaluation reuse.** Each component of the stratification keyed by its rules and the
   fingerprints of the components it reads; unchanged components copy their relations, a component that
   only gained rules continues semi-naive evaluation from its old relations (insertion only; no DRed).
   Expected: a REPL rule or a `%demand` query re-evaluates only the components downstream of the change
   (measure on `examples/typechecker` with its facts and on `strata` with an added rule). Test:
   evaluation equals from scratch under random rule additions.
5. **Cancellation in the language server.** A cancellation flag in `Database`, checked when a query is
   demanded and between compiler phases; `didChange` sets it, waits for the worker to unwind (salsa's
   `cancel_others`), sets the input and schedules publication of the latest version only; requests take
   the same lock. Publication sends a document only when its diagnostics changed. Expected: the last
   keystroke of a burst of *k* on `large` waits for one compile (~450 ms) instead of *k*. Test: an LSP
   transcript with a burst of changes publishes once, equal to the last text from scratch; a unit test
   that a cancelled query leaves no memo.
6. **The object pipeline's shared work.** One dependency graph per program for stratification,
   completeness and termination (7 % of a `large` edit); then the termination verdict of a recursive
   component memoised across revisions by its rules up to spans (11 %). Expected: `large` rule edit
   −30 to −75 ms. Test: `SizeChangeSuite`, `--explain-termination` goldens unchanged; counts of verdict
   computations under an edit outside the component.
7. **Declaration and library firewalls**, in two steps. (a) Item results refer to declarations by stable
   key, and `Moved` rebases an item elaborated on an earlier declarations' core onto the current one.
   (b) `Signatures` exposes per-declaration fingerprints (type, value or case tree, and the fingerprints
   of the declarations they mention, so a change propagates along the uses as with dependent types it
   must); `ElabItem` depends on the fingerprints of the globals it used (`ElaboratedItem.used`) and on
   the names it looked up, found or not, instead of on `Signatures`. The same for a program over a
   library's exported names (zinc's name hashing, within a process). Expected: `large` declaration edit
   869 → ~450 ms, add a declaration 927 → ~450 ms, a library edit in `split` 623 → ~430 ms. Test:
   `ItemQueriesSuite` "editing a declaration elaborates the items that use it" (counts), random edits
   that rename and retype declarations. Risk: medium; the fingerprints must include everything a use
   can unfold.
8. **Reuse of the module-wide expansion** (prototype first, then decision). Applications of meta
   functions during `expandModule` memoised across revisions for one declarations' core (the same
   `ElaboratedDeclarations` object), keyed by normal forms that mention only that core's globals.
   Expected: up to half of a `meta_scaled` rule edit (expansion is 93 %), up to a third of a typechecker
   rule edit; depends on how the directives traverse the module. Risk: high (family instances and metas
   created after the declarations must not enter keys).
9. **`Signatures` by components** (after #91). A chain of per-component queries in #91's topological
   order, each a fork of the previous: Lean's prefix reuse. Expected small on the measured programs
   (`Signatures` 21 ms on `large`, 4–16 ms on meta-heavy small files); measure once #91 has landed.

Order: 1 and 2 are independent and cheapest; 3 is the largest measured gain (the REPL); 5 makes the
language server usable on large files whatever the compile costs; 6 before 7 because it is smaller;
8 needs the designer's decision on its prototype.

## 7. Interactions with #91 and #100

- **#91** (approved, after #100 batch 1; `docs/design/elab-order.md` on `design/elab-order-91`) keeps
  `Signatures` one query per file (its recommendation 7). PR 1 touches `splitItems`, which #91 also
  reorders: whichever lands second rebases. PR 7's fingerprints follow #91's dependency graph (a mention
  depends on the body, recommendation 3) and can be computed per component in its order. PR 9 is
  #91's granularity question deferred to after it, and only if measured.
- **#100** (member functions in module bodies) adds lifted hidden globals (`owner.name`): PR 7's
  stable keys must name them by path. Module bodies stay inside `Signatures`; nothing here changes
  their elaboration or needs #100 to change.

## 8. Sources

- salsa-rs/salsa 30b614d: `src/function/maybe_changed_after.rs` (371–389, 580–647),
  `src/function/backdate.rs` (15–58), `src/runtime.rs` (224–255), `src/durability.rs` (3–20),
  `src/tracked_struct.rs` (214–242, 307), `src/interned.rs` (394), `src/function.rs` (505–512),
  `src/function/memo.rs` (90–97), `src/storage.rs` (150–175), `src/database.rs` (115).
- rust-lang/rustc-dev-guide 20a4fdd: `src/queries/incremental-compilation-in-detail.md` (94–191,
  267–290, 432–480, 497–539).
- rust-lang/rust-analyzer 88552f8: `crates/syntax/src/parsing/reparsing.rs` (1–7, 108, 144),
  `crates/hir-def/src/item_tree.rs` (1–15), `crates/hir-def/src/nameres.rs` (1–30),
  `crates/base-db/src/change.rs` (93–99), `crates/ide-db/src/apply_change.rs` (14).
- leanprover/lean4 b8182f6: `src/Lean/Language/Lean.lean` (80–110, 271, 558–625).
- dotnet/roslyn 7ac1c03: `docs/compilers/Design/Red-Green Trees.md`, `Incremental Parser.md`
  (176–236), `src/Compilers/CSharp/Portable/Parser/Blender.Reader.cs` (215–242),
  `src/Compilers/CSharp/Portable/Declarations/DeclarationTable.cs` (15–22).
- sbt/zinc 5256804: `internal/zinc-apiinfo/src/main/scala/xsbt/api/NameHashing.scala` (29–38),
  `internal/zinc-core/src/main/scala/sbt/internal/inc/IncrementalNameHashing.scala` (71).
- TimelyDataflow/differential-dataflow aa8745f: `differential-dataflow/src/operators/iterate.rs` (1–12).
- Papers: Hammer, Phang, Hicks, Foster, "Adapton", PLDI 2014; Hammer et al., "Incremental computation
  with names", OOPSLA 2015; Acar, "Self-adjusting computation", PhD thesis, CMU 2005; Acar, Blelloch,
  Blume, Harper, Tangwongsan, "An experimental analysis of self-adjusting computation", TOPLAS 2009;
  Gupta, Mumick, Subrahmanian, "Maintaining views incrementally", SIGMOD 1993; McSherry, Murray, Isaacs,
  Isard, "Differential dataflow", CIDR 2013; Ryzhyk, Budiu, "Differential Datalog", Datalog 2.0, 2019.
- Hugin 348fd8e: `query/Database.scala`, `query/CompilerQueries.scala`, `query/ProgramQueries.scala`,
  `core/ProgramElab.scala`, `core/elab/Items.scala` (35–67, 107–114), `compiler/Compiler.scala`,
  `lsp/HuginLanguageServer.scala`, `repl/Session.scala`, `runtime/Evaluation.scala`,
  `docs/INCREMENTALITY.md`, `docs/PERFORMANCE.md`; `docs/design/elab-order.md` on `design/elab-order-91`.
