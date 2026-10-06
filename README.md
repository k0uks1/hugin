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

Requirements: JDK 17+ and [sbt](https://www.scala-sbt.org/) 1.10. The implementation is written in Scala 3;
the only library dependency is munit (tests).

```
sbt compile                       # build
sbt test                          # golden tests (tests/run, tests/neg, tests/pos)
bin/hugin run examples/graphs.hgn # the launcher builds on first use (HUGIN_REBUILD=1 to rebuild)
```

```
usage: hugin <command> [options] <file.hgn>

commands:
  run <file>          compile and evaluate; print output relations and query answers
  check <file>        compile only and report diagnostics
  phases              list the compiler phases
  explain <code>      explain a diagnostic code (e.g. E0401)

options:
  --facts <file>      load ground facts for input relations (repeatable)
  --budget <n>        round budget for components with %partial relations (default: unbounded)
  --print-after <p>   print the program after phase p (comma-separated, repeatable; `all`)
  --stop-after <p>    stop compilation after phase p
  --stats             print evaluation statistics
  --all-relations     print the facts of every relation (including constructors and demand relations)
  --color / --no-color
  --no-warnings       suppress warnings
  --lint              enable advisory checks (W0004)
```

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
  util/      Source, Span, rustc-style diagnostics, error-code catalog
  syntax/    lexer, parser, surface trees, printer
  core/      Context, CompilationUnit, Phase / MiniPhase / MegaPhase
  meta/      symbols, namer, typer (stage inference + meta typing), elaborated trees, evaluator, monomorphization
  obj/       object types and trees, type operations, directives, object typer, moding, elaboration, checks
  runtime/   core IR, lowering, engine, input facts
  driver/    phase plan, runner, CLI glue (Main.scala)
```

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

`tests/` holds golden tests in the style of dotty's test suite:

- `tests/run/X.hgn` — compiled and run; stdout (and warnings, as `//` lines) must equal `X.check`.
  `X.facts` is loaded as input; `X.flags` holds extra options (e.g. `--budget 1`).
- `tests/neg/X.hgn` — must fail; the rendered diagnostics must equal `X.check` (with `X.facts`, the
  failure may come from loading the input).
- `tests/pos/X.hgn` — must compile without errors.

The conformance suite of Appendix A.2 is `tests/run/a01..a12` and `tests/neg/a05..a11`; the examples of
Section 13 are `examples/*.hgn` (also run as `tests/run/ex_*`). To (re)generate check files, delete them and
run `sbt test` once (missing check files are written and the test fails), or set `HUGIN_UPDATE_CHECKS=1`
in the environment of the test JVM.

## Notes

`docs/NOTES.md` records implementation decisions, deviations from the definition, and observations
about the draft (including a gap in the ordering argument of Proposition 8.8 found while implementing it).
