# Triage of the early umbrella issues after the redesign

**Historical.** Written in redesign Phase D (issue #40) to close or hand over the umbrella issues opened
before the redesign: #1, #2, #4, #5 and #7. For each theme it lists what the work since then resolved, what
remains, and which newer issue should take the rest. The newer issues are #53 (parser), #54 (LSP for the
meta level), #56 (typed representation of object code), #60 (performance), #61 (standard library), #63
(reference editorial pass), #65 (termination checker), #66 (elaborator quality), #67 (clause compilation)
and #49 (the language reference). Where a remaining point is a statement the language reference has to
make, the target is #49 rather than a code issue.

State as of the merge of PR #69 into the development branch. "Checked" means the behaviour was tried
on that state with `hugin run`.

## #1 Soundness and theory issues in the language definition (collection)

Most items concerned the interaction of subfact closure, relation modes and the demand transformation.
The redesign removed that interaction: every constructor is a fact constructor (REDESIGN D1), relations
have no modes and demand is ordinary rules (D2), and termination is a hard rule checked by size change
(D3).

| item | status | remaining / target |
|---|---|---|
| A1 nested head constructors and the evaluation order (Prop. 8.8) | resolved by split rules (PR #36): a fact term asserted in a head of a later component is also derived in its constructor's component; since C3 for all constructors (`docs/NOTES.md`, "Nested head constructors") | state the evaluation order in reference: object/facts (#49) |
| A2 rules that read and construct the same fact relation | resolved: the split rule belongs to the constructor's component and is checked for termination like any rule (`tests/neg/t_termination_ctor_source.hgn`, `t_termination_fact_head.hgn`) | the soundness argument belongs in reference: object/termination (#49) |
| B1 ascription typing circular for variables | decided: the ascribed position's column type (`docs/NOTES.md`, "Ascriptions") | state it in the reference (#49) |
| B2 brace disambiguation | implemented: scan for `,` / `.` / `}` at depth 0 | grammar in reference: lexical-structure (#49); parser review in #53 |
| B3 stage independence is observable for undefined results | unchanged by design: an undefined object-level fold is W0001 (the rule never fires), the same expression at the meta level is E0909 where its value reaches object code (`tests/run/a11_stage_independence`, `tests/neg/a11_stage_overflow`). An unused meta definition with an undefined value is not reported. | decide and state in reference: meta/staging (#49) |
| B4 disjunction inside aggregates | implemented: lifted into an auxiliary relation whose rules inline the binding context (F1 below) | the fallback case is still rejected (F1); no newer issue fits, open a focused issue (disjunction in core aggregates) or keep it under #40 |
| B5 queries with several alternatives | decided: answers are united (`docs/NOTES.md`, "Query answers") | reference: object/rules (#49) |
| B6 modes of calls under `not` | moot: no relation modes; `%demand` generates positive demand rules | none |
| B7 moded numeric termination needs a syntactic bound | moot: the moded case is gone; interval reasoning derives bounds through `A = N - 1` for (A) and (B) | none |
| B8 anchoring wording | moot in its old form; (B) requires each variable of the measure to be bound by finite sources outside the component | reference: object/termination (#49) |
| B9 constructive rules, clause (a) | decided and refined (F3): arguments themselves count; ground and matched terms do not | reference: object/termination (#49) |
| B10 membership of open family instances | families are instantiated per closed arguments by the new meta level; whether instantiating `list[int]` still instantiates `cons[int]` for membership was not re-checked | check, then state in reference: meta/families (#49); code changes in #66 |
| B11 which type first-order matching infers | superseded: implicit arguments are solved by pattern unification in the new elaborator, not first-order matching on terms | state the canonical choice in reference: meta/families (#49); unifier quality in #66 |
| B12 floats | decided: division by zero is undefined, NaN is not produced (`docs/NOTES.md`, "Primitives") | reference: object/rules (#49) |
| C1 functor bodies are not object-typed once | unchanged: object-level typing runs on the staged program; errors carry the call chain | #56 (typed representation of object code) |
| C2 `⇑τ ≤ ⇑τ'` at the meta level | unchanged: deferred to the object level | #56 |
| C3 dependent application to non-static arguments | resolved by the dependent meta level (NbE, generative module bodies per item, Phase B) | none |
| C4 implicit parameters constrained only by object variables | partly: such an argument stays unknown and is reported at staging (E0909), not as E0206 (`docs/NOTES.md`, "Open issues (after Phase B)") | #66 |
| C5 requirements checked at evaluation time | unchanged: signature requirements (`%complete edge`) are recorded by staging and checked by the `directives` phase | decide and state in reference: modules (#49) |
| F1 disjunction in an aggregate in a recursive rule | fixed for the common case (context formulas that do not depend on the head); the fallback, where the inputs are bound only through the head's component, is still E0601 (`tests/neg/f_aggregate_disjunction_cycle.hgn`); the fuzz generator avoids it | as B4 |
| F2 `%mode` can change answers | moot: demand rules assert like any rule; `%demand` is visible in the program (`--print-after stage`) | none |
| F3 ground head terms count as constructive | fixed (PR #18 and A1) | none |
| F4 `nil` in comparisons | fixed: both sides of a comparison have one type; E0206 suggests a correct ascription | none |
| meta-level bugs found in the demand-library experiment (comment of 2026-10-07) | the old meta level was deleted in B3; on the new one (checked): `(e).l` still does not parse as a projection (`(r).a` is read as `(r)` applied to something, E0901 and E0101); there is no object formula `true` (`true` is now the meta `bool` constructor, E0902); the other three (dependent signature ascription, imported signature as a type, `_` renaming in formula functions) were not re-checked | `(e).l`: #53; `true` as a formula: #61 (a prelude/stdlib formula) or the reference (#49); the rest: re-check under #66 |

**Suggested action:** close #1 with a link to this file. Open points move to #49 (statements for the
reference), #53, #56, #61 and #66 as listed; B4/F1 needs a home.

## #2 Improve the termination checker

| proposal / limitation | status |
|---|---|
| numeric anchors purely syntactic | resolved: interval reasoning over the canonical body order (`obj/check/Intervals.scala`) |
| decrease only `u = w ± l` or structural | resolved: division by a literal, lexicographic measures (`%terminates (X, Y) …`, inferred pairs) |
| one argument position per relation; mutual recursion rejected | resolved: one measure per relation of the component, up to four relations, inferred |
| anchors only through atoms outside the component | resolved for finite sources and intervals; anchors through finite (non-recursive) types are not covered |
| self-loops from updates and derivations (A2 of #1) | resolved (split rules, see #1 A2) |
| size-change termination (proposal 3) | done: direction (A), descent along derivations, with the closure of size-change graphs (REDESIGN D3, step A1) |
| better diagnostics, `--explain-termination` (proposals 4, 5) | done: E0603/E0604 name the cycle, why (A) and (B) fail, and the missing guard; `--explain-termination` prints the argument per component |

Remaining, for #65: the cap of 4000 graphs in the closure (subsumption-based size change), multiset
orders, non-linear arithmetic other than division by a literal, anchors through finite types, and
components that need (A) for some relations and (B) for others (`tests/neg/t_termination_mixed_demand.hgn`,
a demand that needs an answer of its own relation). One diagnostic to look at there: for the
non-decreasing `len` without `%terminates`
(`tests/neg/a06_termination_nondecreasing_inferred.hgn`) the help suggests an integer bound on the
length (`add a guard such as M < 100`) although the cause is the list argument that does not decrease.

**Suggested action:** close #2; #65 takes the remaining points.

## #4 Query-able compiler (demand-driven, incremental)

| goal | status |
|---|---|
| query engine: memo tables, dependency tracking, cycles, early cut-off | done: `query/Database` (red-green revalidation, eviction), `DatabaseSuite` |
| phases as queries; batch driver as a thin client | done: `SourceText` → `Parse` → `ParseProgram` → `Compile` → `Evaluate`; the CLI, REPL and LSP are clients |
| per-item incrementality | done for parsing and elaboration: libraries as a chain, declarations together, each object item on its own (`docs/INCREMENTALITY.md`) |
| position queries (hover, definition, references, completion) | done: `SemanticIndex` and `query/Ide` |
| invalidation tests | done: `IncrementalSuite` (incremental equals from scratch under edits) |

Remaining: staging and the object-level phases run on the whole program after an edit; an object item
depends on all declarations of its file (per-declaration dependencies were not ported to the dependent
meta level). Both are performance work for #60; what the editor needs from them is #54.

**Suggested action:** close #4; #60 takes the finer-grained queries.

## #5 Syntax highlighting and a language server

| part | status |
|---|---|
| TextMate grammar, VS Code extension, `.vsix` built in CI | done (`editors/vscode`, job `vscode`) |
| diagnostics with codes, related information and the call chain | done; `codeDescription` links the error index of the reference (#49) |
| hover (meta types, object types, staging, family instances), definition, references, symbols, completion, semantic tokens | done |
| code actions from suggestions | done, machine-applicable ones preferred |
| transcript tests over stdio | done (`tests/lsp`, `TranscriptSuite`) |

Remaining, for #54: features for the new meta level (dependent types in hover, holes, quoted patterns,
directives as meta functions, `where`), semantic tokens that separate object and meta variables after the
redesign, and a check that the TextMate grammar covers the new syntax (clauses, `where`, `⇑`, `⟨ ⟩`, `$`,
`[a, b]`, `::`).

**Suggested action:** close #5; #54 takes the rest.

## #7 Integrate fuzz testing

| part | status |
|---|---|
| mutation fuzzing of sources | done (`MutationFuzzSuite`) |
| generated well-typed programs | done (`ProgramGen`, `GeneratedFuzzSuite`), with bound columns and `%demand` |
| semi-naive versus naive evaluation | done (`NaiveEvaluator`, also for bound columns) |
| metamorphic properties: renaming, permutation, demand preserves answers | done |
| budget monotonicity | moot: budgets were removed |
| `sbt fuzz`, nightly workflow with random seeds, shrinking | done (`.github/workflows/fuzz.yml`) |
| regressions as golden tests | done by convention (`tests/run/f_*`); failures are written to `target/fuzz-failures/`, not to a `tests/fuzz-regressions/` directory |

Remaining: the generator produces object-level programs only; there is no generation of meta-level
programs (clauses, inductive families, reflection, user directives), so stage independence (Prop. 3.1)
and the elaborator are covered only by mutation. The generator still avoids the B4/F1 fallback. A
meta-level generator fits #66 (elaborator quality) or a new issue; the B4/F1 case goes with #1 above.

**Suggested action:** close #7; open a follow-up for meta-level program generation, or add it to #66.
