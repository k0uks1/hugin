# Hugin — reference implementation

A reference implementation of **Hugin**, the two-level typed Datalog with first-class facts described in
*Hugin: A Two-Level Typed Datalog with First-Class Facts — Formal Language Definition (Draft, revision 7)*.

It implements the whole pipeline of the definition: parsing, stage inference and meta typing, meta
evaluation (modules, functors, formula functions, type definitions), monomorphization of families,
object-level typing and moding, object-level elaboration (records, disjunction, demand transformation,
derivations), the stratification / completeness / termination checks, compilation to the core IR of
Section 9.3, and a semi-naive interpreter over an interning store. An efficient Datalog engine is out of
scope; the interpreter is meant to make programs runnable and results comparable.

```
$ bin/hugin run examples/typechecker.hgn --facts examples/typechecker.facts
result (lam "f" (arrow (base "int") (base "bool")) (lam "x" (base "int") (app (ref "f") (ref "x")))) (arrow (arrow (base "int") (base "bool")) (arrow (base "int") (base "bool"))).
result (lam "x" (base "int") (ref "x")) (arrow (base "int") (base "int")).
```

## Building and running

Requirements: JDK 17+ and [sbt](https://www.scala-sbt.org/) 1.10. The implementation is written in Scala 3.

```
sbt compile                       # build
sbt test                          # unit suites and golden tests
sbt stage                         # launcher script in target/universal/stage/bin/hugin (sbt-native-packager)
bin/hugin run examples/graphs.hgn # wrapper that stages on first use (HUGIN_REBUILD=1 to re-stage)
```

Commands come first, options after them (`hugin <command> [options] <args>`):

```
hugin run <file.hgn>      compile and evaluate; print output relations and query answers
hugin check <file.hgn>    compile only and report diagnostics
hugin phases              list the compiler phases
hugin explain <code>      explain a diagnostic code (e.g. E0401)
hugin query <file.hgn> <request> [<line>:<col>]
                          ask the compiler: hover, definition, references (at a position),
                          symbols, diagnostics

  --facts <file>          load ground facts for input relations (repeatable)
  --budget <n>            round budget for components with %partial relations (default: unbounded)
  --print-after <phase>,… print the program after these phases (`all` for every phase)
  --stop-after <phase>    stop compilation after this phase
  --stats                 print evaluation statistics
  --all-relations         print the facts of every relation (including constructors and demand relations)
  --color / --no-color    colour diagnostics
  --no-warnings           suppress warnings
  --lint                  enable advisory checks (W0004)
```

## Dependencies

Infrastructure comes from libraries; what remains hand-written is either the subject of the reference
implementation or something no library does adequately:

| concern | library |
|---|---|
| command-line parsing, usage text | [scopt](https://github.com/scopt/scopt) |
| launcher scripts | [sbt-native-packager](https://github.com/sbt/sbt-native-packager) |
| strongly connected components, topological order, shortest paths | [JGraphT](https://jgrapht.org/) (wrapped in `util/Graphs` for deterministic results) |
| "did you mean" suggestions (edit distance) | [Apache Commons Text](https://commons.apache.org/proper/commons-text/) |
| terminal colours | [fansi](https://github.com/com-lihaoyi/fansi) |
| tests, property-based tests | [munit](https://scalameta.org/munit/), [ScalaCheck](https://scalacheck.org/) via munit-scalacheck |
| formatting | [scalafmt](https://scalameta.org/scalafmt/) |

Kept hand-written, deliberately:

- **Lexer and parser.** Error recovery (resynchronising at item boundaries, accepting an item with a
  missing period, layout-aware hints) and rustc-quality messages are the main requirement; parser
  combinator libraries (fastparse, cats-parse, parsley) give little control over recovery. Production
  compilers such as rustc and dotty use hand-written parsers for the same reason.
- **Snippet layout of diagnostics.** There is no maintained JVM counterpart of Rust's ariadne/miette;
  the renderer is ~100 lines on top of fansi.
- **Interning store and semi-naive engine.** They *are* Section 9 of the definition; the point of the
  reference interpreter is to follow it closely. A real Datalog engine (e.g. Soufflé) could be targeted
  by a separate backend from the core IR.

Output follows Section 9.6: facts of output relations in input-fact syntax, sorted lexicographically,
followed by the answers of each query. Without `%output` directives, only query answers are printed; a
program without queries and outputs prints all plain, non-input relations. A run that used the `Cut` rule
(Section 9.7) starts with a `(* truncated ... *)` line.

## Architecture: mini phases

The compiler is organised like dotty: a `CompilationUnit` carries the program through a list of phases,
each of which can be printed (`--print-after`) or used as a stopping point (`--stop-after`). Rule-level
transformations are `MiniPhase`s, and consecutive mini phases are fused into one traversal by a
`MegaPhase` (currently `records + disjunction`). Analysis phases keep running after errors (ill-formed
rules are reported and dropped, so later phases only see well-formed input); lowering and evaluation run
only on error-free programs.

| phase | section | what it does |
|---|---|---|
| `parser` | 2 | hand-written lexer and precedence-climbing parser with error recovery; `%infix` operators are resolved into applications |
| `namer` | 2.3, 2.5 | scopes, duplicate declarations, classification of items by stage, collection of formula-function clauses |
| `typer` | 3, 4.2–4.4, 4.7, 4.8 | bidirectional stage inference and meta typing: inserts quotes `⟨·⟩` and splices `~(·)`, signature matching, implicit type parameters, named patterns → positional, type definitions (unfolded), arity and label checks |
| `metaEval` | 4.5 | call-by-value evaluation of the meta level; module bodies with fresh prefixes (`roads.path`), hygienic expansion of formula functions, cross-stage persistence, deferred checks of `%complete`/`%mode` requirements |
| `monomorphize` | 4.6 | infers family type arguments by first-order matching, instantiates families and rule families by worklist (`len[int]`), rejects polymorphic recursion |
| `directives` | Fig. 2 | attaches `%mode %terminates %partial %open %input %output %derivations %name` to relations |
| `constFold` | 3.3 | folds literal arithmetic (Prop. 3.1); undefined folds are warnings (the rule never fires) |
| `objTyper` | 5, 6.1, 6.2 | well-formed declarations, subtyping/members, best typing contexts by meets, subsumption checks, projections/updates/joins, ascriptions as checked downcasts |
| `moding` | 6.3 | binding steps, canonical (greedy) order, range restriction for every mode, applicable modes of calls |
| `records` | 7.1 | projections `X.l` and updates `(X with {...})` on closed types → one rule per member |
| `disjunction` | 7.2 | splits disjunctions and multi-head rules |
| `demand` | 7.3 | guards and propagation rules (`typed^d[++-]`) for moded relations |
| `derivations` | 7.4 | derivation relations `@r` / `@r#i` |
| `stratify` | 6.4 | dependency graph, Tarjan components, negative cycles (reported with the cycle) |
| `completeness` | 6.5 | incompleteness propagation and Definition 6.6 (also for queries) |
| `termination` | 10 | constructive rules, growing components, validation of `%terminates` (Def. 10.3) |
| `lower` | 9.3 | compiles core rules to `Scan / Deref / Tag / Eval / Test / Lookup / NotIn / Agg` and `Make / Insert` over registers |

The runtime (`hugin.runtime`) implements Section 9: words are literals or identities `(c, n)`; every
relation is an array of tuples with an interning map and hash indexes on bound columns; components are
evaluated in order by semi-naive iteration with old/delta/full windows (Section 9.5); components with
`%partial` relations obey the round budget; queries run over the final store.

Source layout:

```
src/main/scala/hugin/
  util/            sources and spans, rustc-style diagnostics, error-code catalog, Tarjan's SCCs
  syntax/          lexer, parser (+ ParserPhase), surface trees, printer
  compiler/        Settings, CompilationUnit, Context, Phase / MiniPhase / MegaPhase, the phase plan
  meta/            symbols and scopes, namer, elaborated trees, evaluator, monomorphization
  meta/typer/      the typer, split into traits mixed into one class:
                     TyperBase (state, names), Normalization (substitution, static normal forms),
                     Declarations (object declarations, type definitions), TypeElaboration (object and
                     meta types, signatures, meta subtyping), MetaExpressions (inference, checking,
                     application), ObjectCode (stage inference for terms and formulas), Typer (items, bodies)
  obj/             object-level AST: types and symbols, terms and formulas, primitives, printer
  obj/typing/      type operations, directives, constant folding, object typer, moding
  obj/transform/   records, disjunctions, demand transformation, derivations (Section 7)
  obj/check/       dependency graph, stratification, completeness, termination
  ir/              the core IR (Section 9.3), its printer, and lowering from core rules
  runtime/         interning store, semi-naive engine, loading of input facts, evaluation of a compiled program
  query/           the query database, compiler queries, position queries for tooling (Ide)
  cli/             command-line parsing and the entry point (a client of the query database)
```

## The query layer

`hugin.query` makes the compiler query-able, as the basis for tooling (issue #4):

- `Database` is a small demand-driven, incremental computation engine in the style of rustc's query
  system and salsa. Inputs are set from outside, and queries are memoised together with the inputs and
  queries they read. A later revision revalidates memoised results "red-green": a result is reused if
  its dependencies did not change. A recomputed result equal to the previous one does not invalidate
  its dependents (early cut-off). Cycles are reported with their path. There is no maintained JVM
  library for this; the engine is about 150 lines and covered by `DatabaseSuite`.
- Compiler queries: `SourceText` (input, by path) → `Parse` → `Compile` → `Evaluate` (program and facts
  files). The CLI is a client of the database. Editing a facts file re-evaluates without recompiling.
- `SemanticIndex`, filled by the typer and the object typer, records which symbol every name resolves
  to (including through module paths: `roads.path` resolves to the `path` declared in the body of `tc`,
  `g.edge` to the field of the signature), a description of every symbol, and the inferred type of
  every object variable.
- `Ide` answers position queries on top of it: `hover`, `definition`, `references`, `symbols` (an
  outline with enclosing definitions) and `diagnostics`:

```
$ hugin query examples/graphs.hgn hover 32:27
relation path : g.node -> g.node -> rel
$ hugin query examples/graphs.hgn definition 6:21
examples/graphs.hgn:2:30
$ hugin query examples/graphs.hgn hover 6:27
variable X : city
```

Incrementality is per file for now: a change to a program recompiles that program. Finer granularity
(per item) needs the typer to stop mutating shared symbol state; it is tracked in issue #4.

## Diagnostics

Diagnostics are collected, never thrown: the parser resynchronises at item boundaries, the typer
continues after errors with error types, and object-level phases drop ill-formed rules. Every diagnostic
has a code (`hugin explain E0401`) and is rendered in the style of rustc, with primary and secondary
labels, notes and help. Errors in code generated at the meta level carry the meta-level call chain
(Appendix A.1):

```
error[E0602]: negation or aggregation over the incomplete relation `e`
  --> neg/requirements.hgn:6:27
   |
 6 |   lonely N :- x.edge N _, not x.edge _ N.
   |                           ^^^^^^^^^^^^^^ incomplete relation used negatively
   |
   = note: `e` is declared %open
   = note: the absence of a fact of an incomplete relation means unknown, not false (Definition 6.6)
note: in application of `iso`
  --> neg/requirements.hgn:16:5
   |
16 | a = iso { node = v, edge = e }.
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
```

The diagnostic classes of Appendix A.1 are all distinguished; see `src/main/scala/hugin/util/ErrorCodes.scala`
or `hugin explain <code>`.

## Tests

Two kinds of tests, both run by `sbt test`:

- **Unit suites** (`src/test/scala/hugin/...`, mirroring the main packages): lexer and parser
  (precedence, braces, `%infix`, recovery), shared primitive semantics, type operations (subtyping,
  members, meets), moding, the command-line parser and exit codes, rendering of diagnostics, and
  differential tests of the engine (random graphs against a naive fixpoint, budget monotonicity,
  interning, aggregates).
- **Golden tests** in `tests/`, in the style of dotty's test suite:
  - `tests/run/X.hgn` — compiled and run; stdout (and warnings, as `//` lines) must equal `X.check`.
    `X.facts` is loaded as input; `X.flags` holds extra options (e.g. `--budget 1`).
  - `tests/neg/X.hgn` — must fail; the rendered diagnostics must equal `X.check` (with `X.facts`, the
    failure may come from loading the input).
  - `tests/pos/X.hgn` — must compile without errors.

The conformance suite of Appendix A.2 is `tests/run/a01..a12` and `tests/neg/a05..a11`; the examples of
Section 13 are `examples/*.hgn` (also run as `tests/run/ex_*`). To (re)generate check files, delete them and
run `sbt test` once (missing check files are written and the test fails), or set `HUGIN_UPDATE_CHECKS=1`
in the environment of the test JVM.

## Continuous integration and formatting

`.github/workflows/ci.yml` runs on every push and pull request:

- **Formatting** — `sbt scalafmtCheckAll scalafmtSbtCheck` (configuration in `.scalafmt.conf`).
- **Build and test** on JDK 17 and 21 — compilation with warnings as errors (`CI` set in the
  environment enables `-Werror`, see `build.sbt`), the golden test suite (`sbt test`), and
  `scripts/smoke.sh`, which runs every example through the `bin/hugin` launcher.

Locally:

```
sbt scalafmtAll scalafmtSbt     # format
CI=1 sbt compile test           # what CI checks
scripts/smoke.sh                # CLI smoke test
```

## Notes

`docs/NOTES.md` records implementation decisions, deviations from the definition, and observations
about the draft (including a gap in the ordering argument of Proposition 8.8 found while implementing it).
Open theory and soundness questions are collected in issue #1; planned work (termination checker,
REPL, query-able compiler, editor support, libraries, fuzzing) is tracked as GitHub issues.
