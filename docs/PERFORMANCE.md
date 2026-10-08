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

## Milestones

### P0+P1 (in progress)

* Bench harness and bench set (above).
* `StdlibCache` (`compiler/StdlibCache.scala`): the prelude parsed and elaborated once per process and
  text; used by the query database (`Parse`, `ElabLibrary`) and by direct compilations.
* Size-change termination of meta functions: only the call-graph components with calls recorded since the
  last check are checked again (their verdict depends only on their own calls), and the closure extends
  paths by single calls of their callee.
* `Graphs.components`: Tarjan's algorithm and Kahn's with a priority queue in plain Scala instead of
  JGraphT (also a step towards Scala.js, #58); `GraphsSuite` checks it against the JGraphT implementation.

First effect: prelude elaboration (uncached) 121 → ~73 ms warm; with the cache the targeted suites
(query, golden, repl, lsp, obj SizeChange) take 228 s instead of ~440 s (ItemQueriesSuite 267 → 150 s,
IncrementalSuite 77 → 32 s, SizeChangeSuite 44 → 17 s). Not yet re-measured: everything else.
