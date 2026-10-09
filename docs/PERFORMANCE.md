# Performance (issue #60)

This note records how the compiler's performance is measured, the baseline, and the effect of each
milestone of the performance pass. Targets (issue #60): at least 8× on each of

1. **prelude elaboration**, warm (repeated compile in one JVM) and cold (new JVM, first compile);
2. **end-to-end `hugin check` / `hugin run`** on a fixed bench set (small, meta-heavy, Datalog-heavy,
   large generated programs);
3. **wall time of the test suite** (`sbt test` without the fuzz suites).

Correctness is not traded: every check stays complete, no expected output changes, caches are keyed by
all their inputs, and differential tests compare cached with uncached results.

## Method

* **Machine**: cloud container, 4 vCPUs (Intel Xeon @ 2.80GHz), 15 GB RAM, OpenJDK 21.0.12, sbt 1.10.7,
  Scala 3.3.4. Numbers on other machines differ in absolute terms (the designer's machine runs the
  one-line program cold in ~1.35 s where this one takes ~1.9 s); the factors are what counts.
* **Medians** of several runs; min/max are kept in the raw output.
* **Warm** (in one JVM, after warm-up): `sbt "Test/runMain hugin.bench.Bench warm"`
  (`src/test/scala/hugin/bench/Bench.scala`; `HUGIN_BENCH_RUNS`, `HUGIN_BENCH_WARMUP`). It measures
  - *prelude elaboration (uncached, direct)*: parse and elaborate the prelude with `ProgramElab.prelude`,
    no database, no cache: the elaborator's own speed;
  - *compile one-line program*: `hugin check` of `p : int -> rel.` in process, with a new query database
    each time (what every CLI command and every test does): the prelude's cost as a user sees it;
  - every program of the bench set, `hugin run`/`check` in process.
* **Cold** (a new JVM per run): `bench/cold.sh [launcher]` runs every program of the bench set with the
  staged launcher (`sbt stage`) `RUNS` times (default 5) and prints the medians.
* **Test suite**: `sbt -batch 'testOnly * -hugin.fuzz.*'` after `Test/compile`; the time is sbt's
  "Total time" of the test task; per-suite times from `target/test-reports`.
* **Profiles**: async-profiler 3.0 (`-agentpath:…/libasyncProfiler.so=start,event=cpu,collapsed,file=…`)
  on `Bench loop <what> <n>` (repeats one measurement for a profiler).

### The bench set

Generated programs are written by `sbt "Test/runMain hugin.bench.Bench gen"` with fixed seeds
(`BenchGen.scala`) and committed under `bench/`, so the set stays fixed.

| group | programs |
|---|---|
| small (prelude-dominated) | `bench/small/one.hgn` (check), `tests/run/a01_transitive_closure`, `a05_stratified`, `c1_aggregates` |
| meta-heavy | `tests/run/a04_typechecker` (`%demand`), `a10_meta_applicative` (functors, families), `f_modules`, `c1_roundtrip` (reflection), `c2_module_wide` (module-wide directive), `bench/meta/meta_scaled.hgn` (8 copies of functors + families + 2×`%demand` + reflection, under a module-wide directive) |
| Datalog-heavy | `bench/datalog/tc` (transitive closure, 600-node chain + 600 random edges: 179 700 tuples), `sp` (shortest paths with a `min` bound column on a 60×60 grid), `strata` (negation and aggregates on a 20 000-node random graph) |
| large generated | `bench/gen/large.hgn` (150 programs of the fuzz `ProgramGen`, renamed apart: 4 200 lines), check and run |

## Baseline (f3df996)

### Metric 1 and 2, warm (in one JVM; median of 11 after 5 warm-up runs)

| measurement | baseline |
|---|---:|
| prelude elaboration (uncached, direct) | 121 ms |
| compile one-line program (check, new database) | 156 ms |
| check one-line | 136 ms |
| run a01_transitive_closure | 133 ms |
| run a05_stratified | 165 ms |
| run c1_aggregates | 152 ms |
| run a04_typechecker | 158 ms |
| run a10_meta_applicative | 143 ms |
| run f_modules | 151 ms |
| run c1_roundtrip | 128 ms |
| run c2_module_wide | 141 ms |
| run meta_scaled | 9 561 ms |
| run tc_chain | 847 ms |
| run shortest_grid | 307 ms |
| run strata | 500 ms |
| check gen_large | 16 896 ms |
| run gen_large | 17 310 ms |

### Metric 1 and 2, cold (new JVM per run, staged launcher; median of 5)

| program | baseline |
|---|---:|
| check one-line | 1 901 ms |
| run a01_transitive_closure | 2 072 ms |
| run a05_stratified | 2 134 ms |
| run c1_aggregates | 2 188 ms |
| run a04_typechecker | 2 307 ms |
| run a10_meta_applicative | 2 038 ms |
| run f_modules | 2 213 ms |
| run c1_roundtrip | 2 055 ms |
| run c2_module_wide | 2 101 ms |
| run meta_scaled | 12 110 ms |
| run tc_chain | 3 108 ms |
| run shortest_grid | 2 578 ms |
| run strata | 3 082 ms |
| check gen_large | 16 346 ms |
| run gen_large | 16 777 ms |

For reference: the JVM alone (`java -version`) takes ~50 ms; `hugin --help` ~450 ms (class loading and
static initialisation); in `hugin run` of the one-line program the `elaborate` phase is ~1.4 s cold
(the prelude, run by the interpreter and the JIT).

### Metric 3, test suite

`testOnly * -hugin.fuzz.*`: **463 s** (917 tests). Slowest suites (seconds): ItemQueriesSuite 267,
IncrementalSuite 77, obj.check.SizeChangeSuite 44, GoldenTests 17, FileDiagnosticsSuite 14,
ExplanationsSuite 10, LibraryQueriesSuite 7; all others below 4.

### Where the time goes (baseline)

* **The prelude is elaborated once per compilation** (per query database, and per direct compile):
  every test compiles it again — ItemQueriesSuite compiles each golden program 17 times per random-edit
  test (incremental, from scratch and direct), SizeChangeSuite 600 times.
* **Prelude elaboration** (profile): ~45 % size-change termination of meta functions
  (`SizeChange.checkTermination` re-checked *all* recorded calls after every function, with a quadratic
  closure), ~10 % strongly connected components through JGraphT (a comparator recomputing component
  minima), the rest clause compilation (`buildTree`, `split`), bidirectional checking and declarations.
  In a warm loop half the CPU is still the JIT.
* **Cold runs**: ~0.45 s JVM start-up and class loading, ~1.4 s elaborating the prelude in a cold JVM.
* **meta_scaled** grows super-linearly with the number of `%demand` directives (4 copies 2.9 s, 8 copies
  10.8 s, 30 copies run out of memory): meta functions over large data (the module a `%demand` rewrites)
  are memoised by the *normal forms of their arguments* (`Matching.reduceFunction`), so every recursive
  step of `dmodule` over a module of length *n* reads back the rest of the module: O(n²) time and memory.
* **gen_large**: 17 s, almost all in elaboration (to be profiled).

## Prior art and how it maps to Hugin

For every source: the techniques, where Hugin's equivalent is, whether Hugin already does it, the expected
gain and cost, and why it keeps results identical. The **ranked plan** follows the survey.

### a) Elaboration: smalltt, elaboration-zoo, Lean 4, Agda/Idris 2 interface files

Sources: smalltt README and source (<https://github.com/AndrasKovacs/smalltt>); elaboration-zoo
(<https://github.com/AndrasKovacs/elaboration-zoo>); Lean 4 source (`Lean.Meta` caches, `Lean.Expr`,
`.olean` compacted regions: <https://github.com/leanprover/lean4>, de Moura & Ullrich, *The Lean 4 Theorem
Prover and Programming Language*, CADE 2021); Agda interface serialisation
(`Agda.TypeChecking.Serialise`, hash-consed `.agdai`); Idris 2 TTC files.

| technique | source | Hugin | done? | gain / cost / correctness |
|---|---|---|---|---|
| NbE with closures, de Bruijn levels in values and indices in terms, no substitution | smalltt, zoo | `core/Evaluation`, `Readback`, `Value` (exactly this design) | yes | — |
| **Glued values / lazy unfolding of top-level definitions**: a top-level name evaluates to a pair (folded head, lazily unfolded value); conversion unfolds on demand, read-back keeps the small folded form | smalltt `G {g1, g2}` | `Evaluation.globalValue` unfolds definitions eagerly; `quote` returns full normal forms (meta solutions, error messages, memo keys contain unfolded terms) | no | moderate for programs with large meta definitions; the prelude has few. Cost: a new `Val` case and changes in `force`, `quote`, `unify` (medium). Changes printed terms in diagnostics (would change goldens): **not now**, see "Other opportunities". |
| **Approximate (flex/rigid) conversion**: try spines of equal heads without unfolding first, unfold once on failure | smalltt unification modes | `Unification.unify` always forces both sides fully | no | small at Hugin's sizes; same correctness argument as smalltt (fall back to full unfolding). Medium cost. Later. |
| Eta-short meta solutions, approximate occurs check over active metas only, metas frozen per top-level block | smalltt | `Unification.solve`/`psubst`; metas are never frozen, every fork copies all metas | partly | the *copy* of all metas per item and per `undoOnFailure` is a real cost (below). |
| **Persistent / trail-based meta context**: backtracking restores state in O(changes), forks share the parent's state | Lean 4 `MetavarContext` (persistent maps, `saveState`/`restore`); Agda `TCState` | `Core.undoOnFailure`/`tentatively` copy *every* meta solution and the whole level graph (`Levels.snapshot`) on entry; `Core.fork` copies every `MetaEntry`, family memo, module tables | no | **high on large programs**: O(#metas) per item, per declaration attempt and per coercion attempt (`coeObjectData`), i.e. quadratic in program size (15–20 % of gen_large and of ItemQueriesSuite). Cost: medium (an undo log in `Core` and `Levels`). Correctness: restoring from a log of the assignments made since the checkpoint gives exactly the state the full copy restored. |
| **Caches with O(1) keys**: Lean caches `whnf`, `inferType`, `isDefEq`, `instantiateMVars`; `Expr` nodes carry their hash, so cache lookups do not rehash terms; `ShareCommon` hash-conses | Lean 4 | `Matching.reduceFunction` memoises closed applications by `closedKey` = the *read-back normal forms* of all arguments, recomputed and rehashed on every reduction (also `Families.familyInstance`) | partly (memo exists, keys are O(size)) | **very high on meta-heavy code**: a recursive meta function over a list of *n* items reads back the rest of the list at every step, O(n²) time and memory (meta_scaled: 9 s; 30 copies run out of memory). Fix: compute keys for *data* values (constructor applications, literals, quoted constants) once per value object (identity cache) and intern them into hash-consed ids (O(1) hash and equality). Same memo hits and misses as before, so evaluation results and fresh-name counters are unchanged. Cost: medium. |
| Hash-consing in general | smalltt (rejected: beta-reduction defeats it), Lean `ShareCommon` | none | no | only for memo keys (above); smalltt's argument applies to terms in general. |
| **Serialised elaborated interfaces** loaded instead of re-elaborating; Lean maps `.olean` files as compacted regions (no deserialisation pass); Agda hash-conses `.agdai`; keys are content hashes plus compiler version | Lean `.olean`, Agda `.agdai`, Idris 2 `.ttc`, Scala TASTy | `StdlibCache` (in-JVM memo of the parsed and elaborated prelude, done); no on-disk form | in-JVM: yes | in-JVM: warm one-line compile 156 → 5 ms. On disk: removes the ~1 s of elaborating the prelude in a cold JVM, but needs a serialiser for `Core` (globals with `Val`s and closures, metas, levels, family/module tables, case trees, the semantic index with spans): large cost and a new invariant (format version, compiler build hash). Estimated after milestone 1 (cold one-line ~1.65 → ~1.0 s) and **rejected by the designer**. |

### b) Termination checkers

Sources: Lee, Jones & Ben-Amram, *The size-change principle for program termination* (POPL 2001); Ben-Amram
& Lee, *Program termination analysis in polynomial time* (TOPLAS 2007; the polynomial SCP variant);
Fogarty & Vardi, *Büchi complementation and size-change termination* (LMCS 8(1:13), 2012,
<https://arxiv.org/abs/1110.6183>: subsumption is safe only with a modified criterion); Abel & Altenkirch,
*A predicative analysis of structural recursion* (JFP 2002) and the Foetus checker; Agda
`Agda.Termination.{CallGraph,CallMatrix,SparseMatrix,Order,Termination}` (call matrices over the order
semiring `<, ≤, ?`; sets of incomparable matrices, `Favorites`; per-SCC checking; completion by repeated
composition of the new with the original graph); Hyvernat, *The size-change termination principle for
constructor based languages* (LMCS 2014; SCP with constructors and a bounded depth of call arguments);
Lean 4 structural recursion and well-founded recursion with `decreasing_by` (no size-change; for
contrast); Isabelle's `size_change` and `lexicographic_order` methods (Krauss).

| technique | Hugin | done? | gain / cost / correctness |
|---|---|---|---|
| **Check per SCC of the call graph**; only calls inside an SCC can be on a cycle | meta: `core/elab/SizeChange.checkTermination` (C3 restricted it to SCCs but re-checked all of them after every function); object: `obj/check/Termination` runs per recursive component | meta: **now incremental** (only SCCs with new calls; P0+P1) | the verdict of a component depends only on its internal calls, and calls are only added. Meta SCT: 45 % → 6 % of prelude elaboration. |
| **Completion by composing new graphs with the original calls only** (Agda `completionStep gOrig gThis`) | meta `SizeChange.closure` (now), object `SizeChange.check` (already a work list with base steps) | yes | — |
| **Dedup of graphs** (sets of matrices per pair of functions) | both use sets | yes | — |
| **Subsumption / antichains** (keep only the weakest matrices; Agda `Favorites`) | neither | no | can shrink the closure exponentially, but Fogarty & Vardi show that dropping subsumed graphs is safe only if the idempotent-graph criterion is replaced by Ben-Amram & Lee's (a strict arc on a cycle of the graph's own arcs, checked on all graphs). That changes the criterion's code (risk), and Hugin's closures are small after the SCC fix. **Not in this pass**; see "Other opportunities" (it also removes the object level's closure cap). |
| Bit-matrix / small-matrix representation of call graphs | Agda `SparseMatrix`; ours: `Vector[Vector[Option[Rel]]]` (meta), `Set[Arc]` (object) | no | constant factor; only if profiles show it after the above. |
| **Graph algorithms** (SCCs, topological order) | `util/Graphs.components` via JGraphT, with a comparator that recomputed component minima per comparison | **now Tarjan + Kahn with a priority queue in plain Scala** | 10 % of prelude elaboration; also removes a JVM-only library from the core path (#58); `GraphsSuite` checks the result against JGraphT. |

### c) Coverage and case trees

Sources: Cockx & Abel, *Elaborating dependent (co)pattern matching* (ICFP 2018) and Agda's
`Agda.TypeChecking.Coverage`; Maranget, *Compiling pattern matching to good decision trees* (ML 2008:
column heuristics, no clause duplication blow-up in practice).

Hugin's `core/elab/Clauses`, `SplitProblem`, `CaseTree` follow Cockx & Abel (split on the first
constructor pattern of the first clause; coverage = no branch without clauses). Profile: `buildTree`
~15 % of prelude elaboration, of which most is `SplitProblem.norm`/`env`, which re-normalises every
equation and binding of every clause at every split (`p.norm(core, …)`), and `telescopeOrder` at leaves.
Maranget's heuristics change the *shape* of trees (and so which clauses are reported unreachable, W0006),
so they are out of scope; the normalisation work can be cut without changing trees: normalise lazily
(only equations whose variables the last split solved) — small gain, medium cost; later, if profiles
still show it. Run time of case trees (`Matching.runTree`): branch lookup by linear search over
constructors and `Vector` appends — negligible so far.

### d) Incremental and query-based compilers

Sources: rustc dev guide, *Incremental compilation in detail* (red-green marking, fingerprints, on-disk
query cache: <https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation-in-detail.html>);
salsa (<https://salsa-rs.github.io/salsa/>: early cut-off, durability, LRU of memos).

| technique | Hugin `query/` | done? | gain / cost |
|---|---|---|---|
| Red-green revalidation, early cut-off | `Database.fresh`/`execute` | yes | — |
| **Durability**: inputs that rarely change (the standard library) are tracked apart, so revalidation skips their dependency trees | every revalidation walks all dependencies, including the prelude chain | no | small now (a prelude chain is a handful of memos); useful for the language server; later. |
| Fingerprints (stable hashes) instead of full `equals` for cut-off | `ItemFingerprint`, values compared by `equals` | partly | not hot. |
| On-disk query cache keyed by fingerprints | none | no | same trade-off as `.olean` (a). |
| Shared results across sessions/databases | `StdlibCache` | **yes (P0+P1)** | the prelude, the dominant cost of every compile and every test, is elaborated once per process. |
| Memo keys that are cheap to hash | `ItemKey` holds whole item trees (hashed on every lookup), `Database.fresh` scans the active stack with `==` on keys | partly | not hot in profiles yet. |

### e) Start-up

Sources: JDK AppCDS / dynamic archives (JEP 310, 350, 483 *Ahead-of-Time Class Loading & Linking* from
project Leyden), GraalVM native-image (used by scala-cli and scalafmt-native; Metals and Bloop keep a
long-running server instead). Measured on this machine: `java -version` 50 ms; `hugin --help` ~450 ms
(class loading and static initialisers: `CommandLine.<clinit>`, Scala collections); an AppCDS archive
halves `--help`. **Out of scope by the designer's decision** (no start-up tricks, no native image). What
stays in scope is the compiler's own cold path: elaborating the prelude in a cold JVM (~1 s of the 1.9 s,
mostly interpreter and JIT), and code that only runs once per process. The cold metric is reported both
end-to-end and *minus the JVM floor* (`hugin --help`).

### f) Datalog evaluation (within the scope note)

Sources: Soufflé (semi-naive evaluation, automatic index selection by minimum chain cover: Subotić et
al., *Automatic index selection for large-scale Datalog computation*, VLDB 2018); Datafrog
(<https://github.com/rust-lang/datafrog>: sorted relations, leapjoin); Ascent (Sahebolamri et al., CC 2022).

`runtime/Engine` already does semi-naive evaluation with old/delta/full windows over insertion-ordered
identities, and hash indexes on the bound columns of each scan chosen at lowering (`prog.indexes`). In
scope and simple: avoid per-tuple allocation in the inner loop (`range` returns a tuple, `eval` returns
`Option`, `Key` arrays for every index probe, `NonFact` vectors); evaluate a rule's delta variant only
when the delta of that atom is non-empty (rule skipping, as in Soufflé's generated code); index probes on
constant columns. Out of scope: index selection by chain cover, leapjoin/WCOJ, parallelism, codegen.
Datalog evaluation is 30–60 % of the Datalog-heavy runs; the rest is compilation.

## Ranked plan

Ranked by expected gain on the three metrics, against cost and risk. Every step keeps all checks complete
and outputs identical; each cites its source in the code.

1. **Prelude shared per process** (salsa/rustc cross-session reuse; Lean/Agda interfaces in memory) —
   done (`StdlibCache`); remaining: the tests' own direct loaders (ItemQueriesSuite, LibraryQueriesSuite)
   parse the prelude themselves and so miss the cache — use the shared parse there. *Gain: metric 3
   (direct compiles are 35 % of ItemQueriesSuite), metric 1 warm. Cost: trivial. Risk: none (differential
   tests).*
2. **Memo keys for closed meta applications in O(1)** (Lean: cached hashes, `ShareCommon`): identity
   cache of the keys of data values, hash-consed key ids (`Matching`, `Families`). *Gain: meta_scaled
   9 s → expected well under 1 s; removes the O(n²) memory of `%demand` on large modules. Cost: medium.
   Risk: low (same hits as before; differential test of keys against `quote`).*
3. **Undo log instead of full snapshots; forks that share the parent's metas** (Lean persistent
   `MetavarContext`, Agda `TCState`): `Core.undoOnFailure`, `tentatively`, `Levels.snapshot`,
   `Core.fork`, `ElabState.fork`. *Gain: gen_large and every per-item elaboration (15–20 % now, growing
   with program size). Cost: medium. Risk: low-medium; differential: the incremental suites compare
   item-wise with whole-program elaboration already.*
4. **Cold path of the compiler**: measure what runs once per process (static initialisers, `CommandLine`,
   explanations, first use of the parser and elaborator) and remove avoidable work. (An on-disk
   elaborated prelude, `.olean`-style, was estimated after milestone 1 and rejected by the designer.) *Gain: metric 1 cold, all of metric 2 cold.
   Cost: small.*
5. **Clause compilation**: normalise only what a split changed (`SplitProblem.norm`), cache the
   telescope order. *Gain: prelude and meta-heavy elaboration ~10 %. Cost/risk: medium/low.*
6. **Evaluator** (scope note): allocation-free inner loop, skip delta variants with an empty delta,
   constant-column probes. *Gain: Datalog-heavy runs 1.5–2× on evaluation. Cost: small. Risk: low
   (golden tests, the fuzz suites' naive-evaluator differential test).*
7. **Remaining test-suite cost**: re-profile the suites after 1–3 (IDE probes, `Database` revalidation).

## Other opportunities found

Not performance work; recorded for issues (not implemented here).

1. **Size-change with subsumption and the Ben-Amram–Lee criterion** — where: `obj/check/SizeChange.check`
   gives up (rejects) when the closure exceeds `MaxGraphs = 4000`; `core/elab/SizeChange` computes full
   closures. Source: Fogarty & Vardi 2012; Agda's `Favorites`. Follow-up: keep only weakest graphs and
   check the polynomial-time criterion; removes the cap (a program can currently be rejected only because
   its closure is large) and makes the meta checker robust to many mutually recursive functions.
2. **Richer orders in the meta-level size-change check** — `core/elab/SizeChange.compare` knows only the
   constructor-subterm order (`<` for a proper subterm, `≤` for an equal argument), while the object
   level already uses interval reasoning for integers. Agda's `Order` additionally has `Mat` (a nested call
   matrix for arguments under constructors, so `f (c x y) → f (c y x)`-style permutations under a
   constructor are tracked), and Hyvernat's SCP for constructor languages tracks bounded-depth
   constructor contexts. Follow-up: collect meta functions that users write and the checker rejects,
   and decide whether nested matrices are worth it.
3. **Glued evaluation for diagnostics** — `quote` returns fully unfolded normal forms, so error messages
   and `--print-after elaborate` show unfolded definitions where a user wrote a name. Source: smalltt's
   glued values (folded form for display, unfolded for conversion). Follow-up: a glued `Val` for top-level
   definitions; would improve messages (and change goldens).
4. **Approximate/flex-rigid unification** — `Unification.unify` unfolds both sides before comparing equal
   heads; smalltt first tries spines without unfolding. Mostly a performance item, but it also gives
   smaller meta solutions (better messages). Source: smalltt.
5. **Frozen metas per top-level block** — every fork copies all metas of the declarations; smalltt freezes
   the metas of earlier blocks (they can no longer be solved), which is also a scoping guarantee (a later
   item cannot solve an earlier item's meta). Source: smalltt. Follow-up: assert it in `ProgramElab.item`.
6. **Durability in the query database** — library inputs (the prelude, imported files that are not open
   in the editor) as high-durability inputs, so revalidation after an edit skips them. Source: salsa.
7. **Maranget-style heuristics for clause compilation** — splitting on the first constructor pattern of
   the first clause can produce larger trees and more W0006/E0911 cascades than a column heuristic;
   Agda keeps the first-clause rule for its semantics (first-match), so any change needs a semantic
   decision. Source: Maranget 2008; Cockx & Abel 2018.
8. **Index selection by chain cover** — `ir/Lower` picks one index per scan pattern; Soufflé shares
   indexes across patterns with a minimum chain cover of the column sets. Only matters for memory on
   large inputs. Source: Subotić et al. 2018.

## Milestones

### Milestone 1 (`feat/perf-1`): prelude per process, memo keys, trails, linear-time elaboration steps

Changes (each cites its source in the code):

* **Bench harness and bench set** (above).
* **`StdlibCache`** (`compiler/StdlibCache.scala`; salsa/rustc reuse of results, Lean/Agda interfaces in
  memory): the prelude parsed and elaborated once per process and text, used by the query database
  (`Parse`, `ElabLibrary`) and by direct compilations; the tests' direct loaders use the shared parse.
* **`TreeOps.nodes`** with an explicit stack: walking a list (a product `head :: tail`) through nested
  iterators made every step cost the depth, quadratic in the number of a file's items (it collected the
  `%import`s of every compiled file: 40 % of ItemQueriesSuite, most of gen_large).
* **Meta size-change termination** (`core/elab/SizeChange.scala`; Agda: per-component checking,
  completion against the original calls): only the components with new calls are checked again, found
  from the call graph kept between checks; the closure extends paths by single calls.
* **`Graphs.components`** in plain Scala (Tarjan, Kahn with a priority queue) instead of JGraphT.
* **Memo keys in amortised O(1)** (`core/MemoKeys.scala`; Lean 4's cached hashes and `ShareCommon`): the
  read-back of stable data values is cached per value object and normal forms get hash-consed ids; the
  memo hits and misses exactly as before.
* **Trails instead of snapshots** (`Core.undoOnFailure`/`tentatively`, `Levels`; the WAM trail, Lean 4's
  restorable meta context): backtracking costs the changes made, not the number of metas and levels.
* **Copy-on-write metas and persistent names in forks** (`Core.fork`, `elab/NameScope.scala`,
  `ElabState`; Lean 4/Agda persistent elaborator state): forking for one item costs nothing per meta or
  name; `Items.itemTransaction` logs first writes instead of copying all names.
* **Linear-time steps**: `Items.elabInDependencyOrder` counts declaring items once per round instead of
  listing all others per item; `SplitProblem.env` computed once.

Correctness guards added: `StdlibCacheSuite` (cached vs uncached `hugin run` on a sample of golden
programs, the shared base unchanged by compilations, one elaboration per text, uncached prelude equal to
the shared one); `GraphsSuite` (against JGraphT on random graphs); `TreeOpsSuite` (against the recursive
definition on the prelude and all goldens); `MemoKeysSuite` (keys, closedness and id equality against
the definitions they replace); `BacktrackingSuite` (`NameScope` against a `LinkedHashMap` with the old
rollback, `Levels` against state copies, on random operations with nested transactions; fork isolation
and undo of `Core`). The fuzz suites pass (short run).

#### Numbers after milestone 1 (same machine and method)

Warm (median of 11 after 10 warm-up runs):

| measurement | baseline | after | factor |
|---|---:|---:|---:|
| prelude elaboration (uncached, direct) | 121 ms | 54 ms | 2.2× |
| compile one-line program (check, new database) | 156 ms | 4.6 ms | 34× |
| check one-line | 136 ms | 4.8 ms | 28× |
| run a01_transitive_closure | 133 ms | 10.0 ms | 13× |
| run a05_stratified | 165 ms | 13.6 ms | 12× |
| run c1_aggregates | 152 ms | 10.1 ms | 15× |
| run a04_typechecker | 158 ms | 24.2 ms | 6.5× |
| run a10_meta_applicative | 143 ms | 10.0 ms | 14× |
| run f_modules | 151 ms | 17.7 ms | 8.5× |
| run c1_roundtrip | 128 ms | 10.6 ms | 12× |
| run c2_module_wide | 141 ms | 10.5 ms | 13× |
| run meta_scaled | 9 561 ms | 842 ms | 11× |
| run tc_chain | 847 ms | 710 ms | 1.2× |
| run shortest_grid | 307 ms | 83 ms | 3.7× |
| run strata | 500 ms | 350 ms | 1.4× |
| check gen_large | 16 896 ms | 829 ms | 20× |
| run gen_large | 17 310 ms | 888 ms | 19× |

Cold (new JVM per run, staged launcher, median of 5). `hugin --help` (the JVM floor: start-up, class
loading of the command line) is ~520 ms in both builds; the last column is cold minus that floor.

| program | baseline | after | factor | minus floor: baseline → after |
|---|---:|---:|---:|---|
| check one-line | 1 901 ms | 1 650 ms | 1.15× | 1 381 → 1 130 ms (1.2×) |
| run a01_transitive_closure | 2 072 ms | 1 804 ms | 1.15× | 1 552 → 1 284 ms |
| run a05_stratified | 2 134 ms | 1 861 ms | 1.15× | |
| run c1_aggregates | 2 188 ms | 1 819 ms | 1.2× | |
| run a04_typechecker | 2 307 ms | 1 922 ms | 1.2× | |
| run a10_meta_applicative | 2 038 ms | 1 963 ms | 1.04× | |
| run f_modules | 2 213 ms | 1 825 ms | 1.2× | |
| run c1_roundtrip | 2 055 ms | 1 856 ms | 1.1× | |
| run c2_module_wide | 2 101 ms | 1 925 ms | 1.1× | |
| run meta_scaled | 12 110 ms | 3 706 ms | 3.3× | 11 590 → 3 186 ms (3.6×) |
| run tc_chain | 3 108 ms | 2 730 ms | 1.14× | |
| run shortest_grid | 2 578 ms | 2 290 ms | 1.13× | |
| run strata | 3 082 ms | 2 760 ms | 1.12× | |
| check gen_large | 16 346 ms | 5 008 ms | 3.3× | 15 826 → 4 488 ms (3.5×) |
| run gen_large | 16 777 ms | 5 164 ms | 3.2× | |

Metric 3 (test suite): not re-measured on the whole suite (test-run discipline); the suites touched
while iterating: ItemQueriesSuite 267 → ~85 s, IncrementalSuite 77 → ~8 s, obj SizeChangeSuite 44 →
~17 s, GoldenTests 17 → ~7 s, FileDiagnosticsSuite 14 → ~6 s (single runs).

**Where the cold time goes now** (profile of `hugin check` on the one-line program): of the main
thread's ~1.1 s, elaborating the prelude is ~57 % (it runs once per process, in the interpreter and
the JIT's first tiers; warm it takes ~50 ms), parsing it ~6 %, class initialisation ~18 % (Scala
library, `CommandLine`, the elaborator's traits). Making the elaborator faster helps the cold run only a
little; removing the prelude's elaboration from the cold path would need an on-disk elaborated prelude
(an `.olean`-style serialised core, ranked plan step 4; estimated cold one-line ~1.65 → ~1.0 s, minus
the floor ~1.1 → ~0.45 s, for a serialiser of the core state of ~800 lines). **The designer rejected
this option; it is not considered.** The estimate is kept here for the record.

### Milestone 2 (`feat/perf-2`): evaluator, remaining elaboration costs, final numbers

Changes:

* **Evaluator** (`runtime/Engine.scala`, `runtime/Store.scala`; within the scope note: same semi-naive
  strategy, simple indexes):
  - `Key.hashCode` was `java.util.Arrays.hashCode`, a polynomial hash under which `(a, b)` and
    `(a + 1, b - 31)` collide: tuples over small integers (node numbers, identities) formed long hash
    chains — a pathological case. Now MurmurHash3 of the elements (consistent with `Key.equals`).
  - Unboxed index buckets (`IntBuf`); the semi-naive window computed inline from the index of the delta
    atom (no closure, no tuple per scan); a scan's index looked up once per scan, not per probe; tuples
    found through the index of the checked columns are not checked again (index equality implies the
    check's `==`); registers and constants evaluated without an `Option` (`word`); `Relation.append`
    with plain loops.
  - A delta variant of a rule is skipped when its delta atom's delta is empty (Soufflé does the same).
* **Elaboration**: `Reflective.reflectiveGlobals` repeats its lookup of ~50 names only after the names
  changed (`NameScope.version`); meta size-change calls are printed only for a reported E0912;
  `SplitProblem.telescopeOrder` reads back each type once; `MemoKeys` builds the shapes of frequent
  terms directly.
* **Start-up**: `hugin --help`'s usage text is rendered when shown.
* The on-disk elaborated prelude was estimated and rejected by the designer (see milestone 1).

Correctness: golden, runtime, IR, fuzz (short run, including the naive-evaluator differential test),
core, compiler, CLI and util suites; the whole non-fuzz suite at the end (928 tests, all pass).

#### Final numbers (after milestone 2; same machine and method)

**Metric 1, prelude.** The warm uncached elaboration is the elaborator's own speed (no cache); the warm
one-line compile is what a compilation pays for the prelude in a running JVM (the process-wide cache);
both measured with the same harness on the baseline and the final build, after 5 and after 30 warm-up
runs (median of 21):

| measurement | warm-up | baseline | final | factor |
|---|---|---:|---:|---:|
| prelude elaboration (uncached, direct) | 5 | 94 ms | 48 ms | 2.0× |
| prelude elaboration (uncached, direct) | 30 | 64 ms | 28 ms | 2.3× |
| compile one-line program (check, new database) | 5 | 138 ms | 7.2 ms | 19× |
| compile one-line program (check, new database) | 30 | 125 ms | 5.0 ms | 25× |
| cold `hugin check` one-line (new JVM, median of 5) | — | 1 901 ms | 1 471 ms | 1.3× |
| cold minus the JVM floor (`hugin --help`, ~520 ms) | — | 1 381 ms | ~950 ms | 1.45× |

**Metric 2, bench set** (warm: median of 11 after 10 warm-up runs; cold: new JVM, median of 5):

| program | warm baseline | warm final | factor | cold baseline | cold final | factor |
|---|---:|---:|---:|---:|---:|---:|
| check one-line | 136 ms | 6.2 ms | 22× | 1 901 ms | 1 471 ms | 1.3× |
| run a01_transitive_closure | 133 ms | 11.7 ms | 11× | 2 072 ms | 1 718 ms | 1.2× |
| run a05_stratified | 165 ms | 15.3 ms | 11× | 2 134 ms | 1 760 ms | 1.2× |
| run c1_aggregates | 152 ms | 11.0 ms | 14× | 2 188 ms | 1 863 ms | 1.2× |
| run a04_typechecker | 158 ms | 29.6 ms | 5.3× | 2 307 ms | 2 047 ms | 1.1× |
| run a10_meta_applicative | 143 ms | 16.3 ms | 8.7× | 2 038 ms | 1 878 ms | 1.1× |
| run f_modules | 151 ms | 17.0 ms | 8.9× | 2 213 ms | 1 801 ms | 1.2× |
| run c1_roundtrip | 128 ms | 8.8 ms | 15× | 2 055 ms | 1 846 ms | 1.1× |
| run c2_module_wide | 141 ms | 11.1 ms | 13× | 2 101 ms | 1 881 ms | 1.1× |
| run meta_scaled | 9 561 ms | 671 ms | 14× | 12 110 ms | 3 246 ms | 3.7× |
| run tc_chain | 847 ms | 321 ms | 2.6× | 3 108 ms | 2 349 ms | 1.3× |
| run shortest_grid | 307 ms | 79 ms | 3.9× | 2 578 ms | 2 433 ms | 1.06× |
| run strata | 500 ms | 272 ms | 1.8× | 3 082 ms | 2 468 ms | 1.25× |
| check gen_large | 16 896 ms | 857 ms | 20× | 16 346 ms | 4 917 ms | 3.3× |
| run gen_large | 17 310 ms | 867 ms | 20× | 16 777 ms | 5 102 ms | 3.3× |

**Metric 3, test suite** (`testOnly * -hugin.fuzz.*`, sbt's total time of the test task):
**463 s → 42 s (11×)**, 917 → 928 tests. Slowest suites now (seconds): ItemQueriesSuite 23 (was 267),
IncrementalSuite 4.4 (77), obj.check.SizeChangeSuite 1.5 (44), LibraryQueriesSuite 1.4, HandoverSuite
1.3, GoldenTests 1.3 (17), FileDiagnosticsSuite 0.8 (14), ExplanationsSuite 0.7 (10). On CI, "Build
and test" went from 7–9 min to ~2.5–3 min after milestone 1 (of which ~2 min compile).

#### Where 8× was not reached, and why

* **Cold runs** (metric 1 cold, all of metric 2 cold for small and meta programs): a new JVM spends
  ~0.5 s before compiling anything (`hugin --help`), and the rest is dominated by running the elaborator
  for the first time — interpreted and JIT-compiled code, where the same work takes ~30–50 ms warm. The
  elaborator's algorithmic costs are gone (warm uncached prelude 2–2.3× faster, everything
  per-compilation 10–25×), but a cold JVM does not profit proportionally. What would change it — an
  on-disk elaborated prelude, or JVM start-up techniques (class-data sharing, native images) — was
  rejected or excluded by the designer.
* **Uncached prelude elaboration** (2–2.3×): what remains is genuine elaboration work spread thinly
  (bidirectional checking of clause bodies ~30 %, clause compilation, evaluation); the next steps would
  be smalltt's glued values and approximate unification (Other opportunities 3–4), which change printed
  terms and need a design decision.
* **Datalog-heavy runs** (1.8–3.9× warm): within the scope note the evaluator keeps its strategy;
  the rest is boxed words, `Key` arrays per probe and tuple, and parsing large facts files with the
  program parser.

#### Remaining opportunities

* ItemQueriesSuite (23 s, now half the suite) is dominated by the JIT and by compiling every golden
  program from scratch 17 times per test; its from-scratch compilations are what it tests.
* `MemoKeys` retains every stable value it read back for the core's lifetime (100–250 MB live on
  meta_scaled); a bounded or weak cache would cut GC pauses at some recomputation.
* Facts files are parsed by the program parser (24 % of `strata`); a dedicated fact reader would be
  faster but must report the same diagnostics.
* The ranked plan's items not done: approximate unification and glued values (also "Other
  opportunities"), size-change subsumption with the Ben-Amram–Lee criterion.


## After #80–#87 (issue #88)

Same machine, method and harness as the final numbers of #60 (warm: median of 11 after 10 warm-up runs,
the prelude median of 21 after 5 and 30; cold: `bench/cold.sh`, new JVM, median of 5). The usual caveat
holds: absolute numbers move by 10–20 % between sessions of the same container, so every factor above
20 % was re-measured *on the same machine at the same time* against a build of the #60 final commit
(a28b1b0) and of the development branch before #88 (82b84e2), with the same harness (median of 21 after
10, two interleaved rounds).

### The stack overflow

`sbt "Test/runMain hugin.bench.Bench warm"` died with a `StackOverflowError` in `run meta_scaled`, after
the programs before it had run in the same JVM. The harness runs in sbt's forked JVM on the main thread,
with the JVM's default 1 MiB stack (the launcher gives 64 MiB, `-J-Xss64m`). The stack trace (7 000
frames with `-XX:MaxJavaStackTraceDepth`) is one cycle repeated ~190 times, once per item of the module:
`ModuleDirectives.rewrite` → `eval` → `app` → `Matching.reduceFunction` → `Matching.runTree` (5–10
nested calls) → `eval` of the clause body `… :: mirror Rest` → `reduceFunction` …: the module-wide
directive `mirror` of the bench program recurses over the module, which the strict evaluator nests on
the JVM stack. Each level cost ~40 frames: `runTree` recursed once per split of the case tree through
`Option.flatMap` (three frames per split), and `mirror`'s first clause, a quoted pattern
`'{ edge $X $Y :- $..B }`, splits about ten times. The overflow is *not* a regression of #80–#87: the
#60 final build overflows the same way with the same harness settings today (it depends on the JIT's
state, which is why `loop meta_scaled` alone passes); #60's numbers were taken on a run that stayed just
below the limit.

The root cause is JVM stack spent per element of a long list. Fixes (no larger stack, nothing caught):

* `Matching.runTree` is a loop (`@tailrec`, no `Option` combinators) and `reduceFunction` straight-line
  code: a meta function's recursion costs a constant number of frames per level, whatever the depth of
  its case tree (mirror over a module: overflow at ~190 items before, ~590 after, cold, 1 MiB).
* `MemoKeys` (keys of the memo of meta applications: read-back of stable data, hash-consed ids,
  closedness) recursed down a list's spine; past a depth of 200 they continue with an explicit stack.
  A module-wide directive over 3 000 items overflowed here even without recursion in the directive.
* `Evaluation.eval` of a chain of applications in argument position (`cons x1 (cons x2 (… nil))`, the
  data of a module that `listData` builds) is a loop, in the same order of evaluation.
* `Reflection.elements` (the items of a list value) is a loop.

`LongListsSuite` runs each case on a thread with the JVM's default 1 MiB stack: a module-wide directive
over a module of 5 000 items, `mirror` over 400 items, and memo keys and evaluation of a list of 100 000
elements (all three overflow before the fix). With the launcher's stack, lists of 10 000 elements pass
through `list.lift`, a recursive directive and a recursive meta function. What remains proportional to a
list's length is a meta function's own recursion (one level per element: the evaluator is a recursive
NbE evaluator), and the parser and elaborator on a source list literal of thousands of elements
(`Slices.congruent`, checking); see docs/NOTES.md (#88).

### Numbers (after #88)

**Metric 1, prelude** (warm, median of 21):

| measurement | warm-up | #60 final | after #88 | change |
|---|---|---:|---:|---:|
| prelude elaboration (uncached, direct) | 5 | 48 ms | 61 ms | +28 % |
| prelude elaboration (uncached, direct) | 30 | 28 ms | 40 ms | +42 % |
| compile one-line program (check, new database) | 5 | 7.2 ms | 7.2 ms | 0 |
| compile one-line program (check, new database) | 30 | 5.0 ms | 4.4 ms | −12 % |
| cold `hugin check` one-line | — | 1 471 ms | 1 570 ms | +7 % |

**Metric 2, bench set**:

| program | warm #60 final | warm after #88 | change | cold #60 final | cold after #88 | change |
|---|---:|---:|---:|---:|---:|---:|
| check one-line | 6.2 ms | 5.3 ms | −15 % | 1 471 ms | 1 570 ms | +7 % |
| run a01_transitive_closure | 11.7 ms | 11.7 ms | 0 | 1 718 ms | 1 736 ms | +1 % |
| run a05_stratified | 15.3 ms | 14.9 ms | −3 % | 1 760 ms | 1 741 ms | −1 % |
| run c1_aggregates | 11.0 ms | 10.6 ms | −4 % | 1 863 ms | 1 807 ms | −3 % |
| run a04_typechecker | 29.6 ms | 29.4 ms | −1 % | 2 047 ms | 1 969 ms | −4 % |
| run a10_meta_applicative | 16.3 ms | 11.8 ms | −28 % | 1 878 ms | 1 834 ms | −2 % |
| run f_modules | 17.0 ms | 18.7 ms | +10 % | 1 801 ms | 1 936 ms | +7 % |
| run c1_roundtrip | 8.8 ms | 9.4 ms | +7 % | 1 846 ms | 1 814 ms | −2 % |
| run c2_module_wide | 11.1 ms | 11.0 ms | −1 % | 1 881 ms | 1 770 ms | −6 % |
| run meta_scaled | 671 ms | 675 ms | +1 % | 3 246 ms | 3 346 ms | +3 % |
| run tc_chain | 321 ms | 349 ms | +9 % | 2 349 ms | 2 325 ms | −1 % |
| run shortest_grid | 79 ms | 111 ms | +40 % | 2 433 ms | 2 329 ms | −4 % |
| run strata | 272 ms | 305 ms | +12 % | 2 468 ms | 2 471 ms | 0 |
| check gen_large | 857 ms | 908 ms | +6 % | 4 917 ms | 4 922 ms | 0 |
| run gen_large | 867 ms | 973 ms | +12 % | 5 102 ms | 5 281 ms | +4 % |

`hugin --help` takes ~450 ms (was ~520 ms in #60's session). Metric 3 (the test suite) was not re-run
(the issue's test policy runs targeted suites only).

### Changes above 20 %, re-measured on the same machine

| measurement | #60 final (a28b1b0) | before #88 (82b84e2) | after #88 |
|---|---:|---:|---:|
| prelude elaboration (uncached, warm-up 10) | 36–45 ms | 55–58 ms | 54–58 ms |
| run shortest_grid (warm) | 67–72 ms | 87–92 ms | 77–83 ms |
| run meta_scaled (warm, `loop`) | 650–661 ms | 604–675 ms | 613–634 ms |

* **shortest_grid** (+25 % before #88): the facts file (14 161 facts) is parsed with the program parser,
  and the resilient parser of #53 collected the `%infix` operators with `toks.sliding(4)` — a vector per
  token. Now a loop over the tokens (`Operators.declared`, same result). The rest (+10–15 %) is the
  parser's own per-token work since #53 (`ParserBase.atColumn0`, `TreeOps.hasSyntaxErrors` per fact);
  recorded, not changed (it is the parser's error recovery).
* **Prelude elaboration, uncached** (+40 %, real; the cached compile that users pay is unchanged): a
  profile of `Bench loop prelude` against a28b1b0 attributes the difference to new work of #80–#87, not to
  a slower algorithm: the meta-level tooling records of #54 (~17 % of the time: `Clauses.recordSplits`
  computes the splittable pattern variables of every clause by index unification against every
  constructor, `flushTooling` runs the records), the derived `lift`/`reify` functions of the shared
  prelude types of #85 (~5 %), and the resilient parser of #53 (~4 %). Making `recordSplits` lazy would
  need it to run against a later state of the metas than the clause's, so it is recorded here rather than
  changed in a bug fix.
* **meta_scaled**: unchanged against #60. A first version of the `MemoKeys` fix (an explicit stack on
  every call) cost +28 % here, from allocations; the walks now recurse up to a depth of 200 and switch to
  the explicit stack only below it.

## Lazy re-export of `std/demand` (#61, batch B2)

A program that does not use `%demand` no longer elaborates `std/demand` (docs/LIBRARIES.md, "Lazy
re-export"). Measured on the machine above at cd50f3e (B1) against B2, while other builds ran (load
average 7 to 10). Thread CPU time is robust to that load; wall times were taken interleaved, base and B2
alternating.

| measurement | B1 | B2 | change |
|---|---:|---:|---:|
| prelude chain elaboration, warm, uncached (thread CPU, median of 31 after 15 warm-up) | 84.9 ms | 45.2 ms | −47 % |
| first prelude chain elaboration in a new JVM (median of 7) | 1 889 ms | 1 307 ms | −31 % |
| cold `hugin check bench/small/one.hgn`, wall (median of 9, interleaved) | 3 938 ms | 2 975 ms | −24 % |
| cold `run a01_transitive_closure`, wall | 4 275 ms | 3 436 ms | −20 % |
| cold `run c1_roundtrip`, wall | 4 418 ms | 3 832 ms | −13 % |
| cold `run a04_typechecker` (uses `%demand`), wall | 3 679 ms | 3 918 ms | within noise |

* The B2 chain is `std/reflect` and the prelude. `std/demand` alone costs 45.2 ms warm on top of
  `std/reflect`, as much as the rest of the chain.
* The check that `std/demand` declares no object constants (its declarations without clauses) costs
  16.7 ms warm and about 100 ms in a new JVM (1 207 ms without it). It runs once per process and is
  included in the B2 numbers.
* A program that uses `%demand` elaborates the same chain as before. The warm cached compile
  (`StdlibCache`) is unchanged.
