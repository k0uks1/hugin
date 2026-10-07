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

### Data and fact constructors

A declaration `c : τ1 -> ... -> τn -> a.` with an open type `a` declares a **data constructor**: `c t̄`
builds a value of type `a`, usable everywhere a term is (rule heads' arguments, nested patterns,
comparisons, aggregate terms, inputs of moded calls), but `c` is not a relation. The modifier `%fact`
declares a **fact constructor**, whose facts can also be read and derived like a relation's:

```
shape : type.
circle : shape.                 (* data *)
%fact square : int -> shape.    (* facts: `seen N :- square N.` reads them *)
```

Reading a data constructor (in a body, `not`, an aggregate or a query), deriving it in a rule head,
naming it in a directive or passing it where a relation is expected is E0406. `%fact` also applies to
structs and to signature fields (`{ t : type, %fact c : int -> t }`, matched by fact constructors only;
a plain constructor field `c : int -> t` is matched by both kinds). The prelude's `nil` and `cons` are
data constructors.

Evaluation: data constructors never assert. A rule adds its head fact and the fact-constructor terms
nested in it (also inside data terms); data values are only hash-consed. Patterns and comparisons are
structural (a term never built compares like any other). A binding equation `X = c t̄` builds the value
if `c` is a data constructor, and checks that `c t̄` is a fact if `c` is a fact constructor. A
fact-constructor term in an input of a moded call is E0504, so `%mode` adds facts only to the moded
relation and its demand relations. See `docs/NOTES.md`, "Data and fact constructors".

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
                          ask the compiler: hover, definition, references, completions
                          (at a position), symbols, diagnostics
hugin repl [<file.hgn> ...]
                          an interactive session, starting with these files (see below)
hugin lsp                 run the language server (LSP over stdin/stdout) for editors

  --facts <file>          load ground facts for input relations (repeatable)
  --budget <n>            round budget for components with %partial relations (default: unbounded)
  --print-after <phase>,… print the program after these phases (`all` for every phase)
  --stop-after <phase>    stop compilation after this phase
  --stats                 print compiler phase timings and evaluation statistics
  --all-relations         print the facts of every relation (including fact constructors and demand relations)
  --color / --no-color    colour diagnostics
  --no-warnings           suppress warnings
  --lint                  enable advisory checks (W0004)
  --explain-termination   print the measure and justification of every recursive component
  --no-prelude            do not include the standard prelude
```

## The REPL

`hugin repl [file.hgn ...] [--facts f]` starts an interactive session. Line editing, history (kept in
`~/.hugin_history`) and completion come from [JLine 3](https://github.com/jline/jline3).

- **Input.** Declarations, definitions, rules and directives extend the session; `?- query.` is answered
  at once against the session and the loaded facts. An item continues over several lines (with a `...`
  prompt) until its terminating period; periods in comments, strings and selections (`roads.path`) and
  inside brackets do not count. Several items may share a line.
- **Errors do not lose state.** An input is accepted or rejected as a whole: if the session with the
  input has errors (also errors the input causes in earlier text, such as a cycle through negation), the
  session stays as it was. Diagnostics are rendered as in batch mode, with lines and columns relative to
  the input as typed (`<input 7>:2:3`) or to the loaded file. A warning is reported once, for the input
  that introduced it; W0003 (unused definition) is not reported, as later inputs are expected to use
  definitions.
- **Commands.**

  | command | |
  |---|---|
  | `:load <file.hgn>`, `:reload` | add a program file to the session; read the loaded program and facts files, and every file they import (transitively), again |
  | `:facts <file>` | load ground facts for `%input` relations |
  | `:type <expr>` (`:hover`) | the type of a name or module path (`:type roads.path`, as hover shows it), of an object term (`:type cons 1 nil`) or of a meta expression (`:type tc { node = city, edge = road }`) |
  | `:kind <name>` | what a name denotes (object type, relation, constructor, meta definition, ...) |
  | `:list` | the accepted inputs, loaded files and facts files |
  | `:imports` | the files the session imports (transitively), in dependency order |
  | `:print <phase> [<name>]` (`:print-after`) | the session after a phase (as `--print-after`), optionally only the items mentioning a name |
  | `:explain <code>` | explain a diagnostic code |
  | `:budget <n>\|off`, `:stats on\|off` | round budget and evaluation statistics |
  | `:reset`, `:help`, `:quit` | start an empty session, list the commands, end the session |

- **Loaded files** keep their identity: a file added with `:load` (or on the command line) is a part of
  the session under its own path, so its `%import`s are resolved relative to it (as when it is compiled
  on its own) and its diagnostics point into it. An input's `%import`s are resolved relative to the
  working directory.
- **Completion** (Tab) offers commands and their arguments, and otherwise asks the compiler
  (`Ide.completions`) at the cursor: names in scope, members after `m.`, directives after `%`, and the
  variables of the item being typed (also before it compiles).

```
$ hugin repl examples/graphs.hgn
loaded examples/graphs.hgn
hugin> ?- from_berlin C.
C = berlin.
C = paris.
C = rome.
hugin> :type roads.path
relation roads.path : city -> city -> rel
hugin> near : city -> rel.
hugin> near C :-
  ...    road berlin C,
  ...    goal C.
error[E0101]: unresolved name `goal`
 --> <input 3>:3:3
  |
3 |   goal C.
  |   ^^^^ not found in this scope
```

The session (`hugin.repl.Session`) is independent of the terminal (`hugin.repl.Repl`). It is a client
of the query layer: the session is a program made of several files (the `Composite` input of the query
database: each input as a virtual file `<input N>`, each loaded file under its path), compiled as one
module body whose items keep their files. Compiling, `:type` (a probe part asked with `Ide.hover`) and
evaluation reuse what did not change: a query or a probe is one more item of the session's program,
elaborated on its own over the session's items, which are not elaborated again. When stdin is not a
terminal, or with `--batch`, inputs are read from stdin without prompts; `--echo` writes each input after
its prompt, which is how the transcript tests run.

## Libraries and the prelude

A source file is a module body. `m = %import "path".` binds the module value of another file, resolved
relative to the importing file (`.hgn` is appended if the path has no extension). A file is elaborated
and evaluated once however often it is imported, so every importer sees the same declarations; it sees
the prelude but not the program that imports it. Its object declarations are named after the file
(`geo.here`). Missing and cyclic imports are errors (E0108).

The prelude, [`prelude.hgn`](src/main/resources/hugin/stdlib/prelude.hgn), is ordinary Hugin source
bundled with the compiler and included in every program (unless `--no-prelude`). It declares the base
types (`int : type = %builtin int.`), lists with `len`, `option`, `pair`, the signature `graph` and the
functors `tc` and `bounded` of Section 13.1. Its names can be shadowed by the program. The design and its
relation to Section 4 are described in [`docs/LIBRARIES.md`](docs/LIBRARIES.md).

## Dependencies

Infrastructure comes from libraries; what remains hand-written is either the subject of the reference
implementation or something no library does adequately:

| concern | library |
|---|---|
| command-line parsing, usage text | [scopt](https://github.com/scopt/scopt) |
| launcher scripts | [sbt-native-packager](https://github.com/sbt/sbt-native-packager) |
| strongly connected components, topological order, shortest paths | [JGraphT](https://jgrapht.org/) (wrapped in `util/Graphs` for deterministic results) |
| "did you mean" suggestions (edit distance) | [Apache Commons Text](https://commons.apache.org/proper/commons-text/) |
| language server protocol, JSON-RPC | [Eclipse LSP4J](https://github.com/eclipse-lsp4j/lsp4j) |
| terminal colours | [fansi](https://github.com/com-lihaoyi/fansi) |
| line editing, history and completion in the REPL | [JLine 3](https://github.com/jline/jline3) |
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
| `imports` | — | loads the prelude and, transitively, every `%import`ed file (in dependency order); missing and cyclic imports |
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
| `stratify` | 6.4 | dependency graph, strongly connected components in dependency order, negative cycles (reported with the cycle) |
| `completeness` | 6.5 | incompleteness propagation and Definition 6.6 (also for queries) |
| `termination` | 10 | constructive rules, growing components, validation of `%terminates` (Def. 10.3, generalised: interval reasoning, lexicographic measures, mutual recursion; see `docs/NOTES.md`) |
| `lower` | 9.3 | compiles core rules to `Scan / Deref / Tag / Eval / Test / Lookup / NotIn / Agg` and `Make / Insert` over registers |

The runtime (`hugin.runtime`) implements Section 9: words are literals or identities `(c, n)`; every
relation is an array of tuples with an interning map and hash indexes on bound columns; components are
evaluated in order by semi-naive iteration with old/delta/full windows (Section 9.5); components with
`%partial` relations obey the round budget; queries run over the final store.

Source layout:

```
src/main/resources/hugin/stdlib/prelude.hgn   the prelude
src/main/scala/hugin/
  util/            sources, slices and spans, rustc-style diagnostics, error-code catalog, graph algorithms (JGraphT)
  syntax/          lexer, parser (ParserPhase), surface trees, printer, generic tree operations (TreeOps),
                   item slices of a file (Slices)
  compiler/        Settings and Display, CompilationUnit, Context, Phase / MiniPhase / MegaPhase, the phase
                   plan, libraries (the prelude and imported files: Libraries, ImportsPhase), the per-item
                   elaboration of a program (ProgramElab), the semantic index for tooling (SemanticIndex)
  meta/            symbols and scopes (Symbols), the typer's symbol table (SymTable), stable keys of items,
                   scopes and symbols (Keys), namer, elaborated trees and their printer, evaluator (MetaEval),
                   monomorphization
  meta/typer/      the typer, split into traits mixed into one class:
                     TyperBase (state, names), Normalization (substitution, static normal forms),
                     Declarations (object declarations, type definitions), TypeElaboration (object and
                     meta types, signatures, meta subtyping), MetaExpressions (inference, checking,
                     application), ObjectCode (stage inference for terms and formulas), Typer (items, bodies)
  obj/             object-level AST: types and symbols, directives of relations (ProgramFacts), terms and
                   formulas, primitives, printer
  obj/typing/      type operations, directives, constant folding, object typer, moding
  obj/transform/   records, disjunctions, demand transformation, derivations (Section 7)
  obj/check/       dependency graph, stratification, completeness, termination (with interval reasoning)
  ir/              the core IR (Section 9.3), its printer, and lowering from core rules
  runtime/         interning store, semi-naive engine, loading of input facts, evaluation of a compiled program
  query/           the query database (Database), the compiler's queries (CompilerQueries), diagnostics by
                   file (FileDiagnostics), position queries for tooling (Ide)
  lsp/             the language server (lsp4j): server and document state, request handlers (Features),
                   position conversion (Positions), file URIs (Uris)
  repl/            the interactive session (Session, testable without a terminal; its parts are Chunks),
                   the reading of inputs (Input) and the JLine front end (Repl)
  cli/             command-line parsing and the entry point (a client of the query database)
```

## The query layer

`hugin.query` makes the compiler query-able, as the basis for tooling (issue #4):

- `Database` is a small demand-driven, incremental computation engine in the style of rustc's query
  system and salsa. Inputs are set from outside, and queries are memoised together with the inputs and
  queries they read. A later revision revalidates memoised results "red-green": a result is reused if
  its dependencies did not change. A recomputed result equal to the previous one does not invalidate
  its dependents (early cut-off). Cycles are reported with their path; diagnostics are accumulated
  outputs of queries; memos that no recent demand reaches are evicted. There is no maintained JVM
  library for this; the engine is about 300 lines and covered by `DatabaseSuite`.
- Compiler queries: `SourceText` (input, by path) → `Parse` → `ParseProgram` → `Compile` → `Evaluate`
  (program and facts files); in between, libraries and the program's items are queries of their own
  (see below). The CLI is a client of the database. Editing a facts file re-evaluates
  without recompiling. A program may be made of several files (the input `Composite`, used by the REPL):
  their items form one module body, and each item keeps its file for diagnostics and for resolving its
  `%import`s.
- `SemanticIndex`, filled by the typer and the object typer, records which symbol every name resolves
  to (including through module paths: `roads.path` resolves to the `path` declared in the body of `tc`,
  `g.edge` to the field of the signature), a description of every symbol, and the inferred type of
  every object variable.
- `Ide` answers position queries on top of it:
  - `hover`: the description of a symbol as seen at that use (through a module path, with the type
    instantiated there: `roads.path : city -> city -> rel`), or the type of an object variable (all
    types if a functor body is instantiated at several);
  - `definition` / `references`: for symbols across module paths; for object variables within their rule;
  - `completions`: names in scope at the position (innermost module body outwards, plus the variables
    of the rule), members after `m.`, labels inside a named pattern `c { ... }`, directives after `%`;
  - `symbols` (an outline with enclosing definitions) and `diagnostics`:

```
$ hugin query examples/graphs.hgn hover 18:27
relation roads.path : city -> city -> rel
$ hugin query examples/graphs.hgn definition 18:27
<stdlib>/prelude.hgn:31:3
$ hugin query examples/graphs.hgn hover 18:16
variable C : city
```

Incrementality is per item for the elaboration: libraries are named and elaborated once and shared by
all programs, the items of a program are parsed from their own text and elaborated one by one, an item
depends on the names and declarations it uses, `FileDiagnostics` gives a compilation's diagnostics by
file from the queries that computed them, and memos no recent demand reaches are evicted. Meta
evaluation and the object-level phases still run on the whole program after an edit. See
`docs/INCREMENTALITY.md` (issue #4).

## Editor support

`hugin lsp` is a language server speaking the
[Language Server Protocol](https://microsoft.github.io/language-server-protocol/) over stdin and stdout
(`hugin.lsp`, built on [LSP4J](https://github.com/eclipse-lsp4j/lsp4j)). It is a client of the query
database: an open document's text is its `SourceText` input, files that are not open (imports) are read
from disk, and every request is answered by `Ide` on the memoised compilation. It provides

- diagnostics for every open document and for the files it imports, published per file (`FileDiagnostics`:
  an imported file's on its own URI, from the queries that elaborated it; those of a file that is not
  open are sent again only when they changed, and cleared when they disappear), with the code, the
  primary label as the range, notes and helps in the message, and secondary labels and the meta-level
  expansion chain as related information (singleton variables and unused definitions are shown faded);
- hover: the meta type of a definition or path, the inferred object type of a variable, and what the
  compiler decided there (below);
- go to definition and find references (through module paths; declarations in the bundled prelude have
  no location and are not returned), the document outline, completion (names in scope, module members
  after `.`, labels in named patterns, directives after `%`) and semantic tokens;
- quick fixes: every suggested edit the compiler attaches to a diagnostic (below).

**Hover** notes come from the semantic index (`compiler/SemanticIndex`), which records them by span:

- *staging* (recorded by the meta evaluator): object code passed where meta code is expected is
  *quoted* (`p X` passes the code `⟨X⟩` to the formula function `p`), meta code used in object code is
  *spliced* (`I.price < 10` in the body of `cheap` inserts the code bound to `I`), and a compile-time
  primitive in object code is *persisted* as a literal (`X = k` with `k : int = 6 * 7` embeds `42`).
  Code in a functor or a formula function is evaluated once per application; every value is shown.
  The innermost staged piece of code around the position is described;
- *family instances* (recorded by monomorphization): a use of `cons`, `len` or `list` shows the
  instance it resolved to (`len[int]`; a use in the body of a family rule may resolve to several), a
  family's declaration lists all of its instances.

```
$ hugin query examples/formula_functions.hgn hover 10:20
meta parameter p : ⇑A -> ⇑prop
spliced: the meta-level code `X.price < 10` is inserted here
$ hugin query examples/lists.hgn hover 4:15
relation len A : list A -> int -> rel
instance: `len[int]`
```

**Suggestions.** Like rustc, a diagnostic can carry machine-applicable suggestions: an edit (a span and
its replacement) with a short message, the most likely first; each comes with a help that describes it in
prose (the rendered output shows the help). The language server offers them as quick fixes, the first one
preferred. They exist for singleton variables (`_` or `_X`), missing labels of a named pattern (`b = _`,
or `..`), a functor that negates over a parameter whose signature lacks `%complete edge` (added to the
signature, inline or named, unless it is in the prelude), a relation without a mode a signature requires
(`%mode f + -.` before its declaration), a name with a similar declaration, a missing period at the end of
a line, and a type definition that is not strict (`%abbrev`).

Positions are converted between the protocol's 0-based lines and UTF-16 columns and the compiler's
character offsets in `lsp/Positions`. Facts files (`.facts`) get syntax diagnostics only.

The server is tested on recorded protocol transcripts (`tests/lsp/X.in`: the client's JSON-RPC messages,
one per line; `X.check`: the normalized transcript with the server's responses and notifications), which
`TranscriptSuite` replays over streams with `Content-Length` framing, as an editor would. Update them
like the golden tests, with `HUGIN_UPDATE_CHECKS=1`.

[`editors/vscode`](editors/vscode) is a minimal VS Code extension: the language configuration
(`(* *)` comments, brackets), a TextMate grammar
([`hugin.tmLanguage.json`](editors/vscode/syntaxes/hugin.tmLanguage.json), also usable by other editors
and GitHub Linguist) and a client that starts `hugin lsp`. To try it:

```
sbt stage                                    # or let bin/hugin stage on first use
cd editors/vscode && npm install
code --extensionDevelopmentPath=$PWD ../..   # or: npx vsce package --skip-license, then install the .vsix
```

and set `hugin.server.path` to `<checkout>/bin/hugin` unless `hugin` is on the `PATH`. Any other LSP
client works the same way: run `hugin lsp` for files with the extensions `.hgn` and `.facts`.

CI packages the extension on every push (job `vscode`); the `.vsix` is the workflow run's artifact
`hugin-vscode` (`code --install-extension hugin.vsix`).

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

Three kinds of tests, all run by `sbt test`:

- **Unit suites** (`src/test/scala/hugin/...`, mirroring the main packages): lexer and parser
  (precedence, braces, `%infix`, recovery), tree operations, stable keys, meta evaluation,
  monomorphization, shared primitive semantics, type operations (subtyping, members, meets), moding,
  stratification, completeness, interval reasoning, lowering, the command-line parser and exit codes,
  rendering of diagnostics,
  differential tests of the engine (random graphs against a naive fixpoint, budget monotonicity,
  interning, aggregates), the query layer, and the language server (position conversion, the
  request handlers on in-memory documents, and one session over piped streams).
- **Golden tests** in `tests/`, in the style of dotty's test suite:
  - `tests/run/X.hgn` — compiled and run; stdout (and warnings, as `//` lines) must equal `X.check`.
    `X.facts` is loaded as input; `X.flags` holds extra options (e.g. `--budget 1`).
  - `tests/neg/X.hgn` — must fail; the rendered diagnostics must equal `X.check` (with `X.facts`, the
    failure may come from loading the input).
  - `tests/pos/X.hgn` — must compile without errors.
  - `tests/repl/X.in` — a REPL session run by `hugin repl --batch --echo`; the transcript (inputs after
    their prompts, output and diagnostics) must equal `X.check`. `X.flags` holds the files to load.
- **Fuzz suites** (`src/test/scala/hugin/fuzz`), a short deterministic run; see below.

The conformance suite of Appendix A.2 is `tests/run/a01..a12` and `tests/neg/a05..a11`; the examples of
Section 13 are `examples/*.hgn` (also run as `tests/run/ex_*`). To (re)generate check files, delete them and
run `sbt test` once (missing check files are written and the test fails), or set `HUGIN_UPDATE_CHECKS=1`
in the environment of the test JVM.

## Fuzz testing

The fuzz suites are ScalaCheck properties (issue #7); a failing input is shrunk by ScalaCheck.

- **Mutation fuzzing** (`MutationFuzzSuite`): the programs of `examples/` and `tests/` are mutated one to
  four times — tokens deleted, duplicated, swapped, replaced or inserted; identifiers renamed everywhere;
  periods removed; brackets unbalanced or mismatched; literals replaced by boundary values (2^63, 1e309,
  invalid escapes, …); lines deleted, duplicated, swapped, moved or the file truncated. Shrinking removes
  tokens. Properties: no uncaught exception, `check` finishes within the time limit with exit code 0 or 1
  and the same diagnostics twice, a failing `check` says why, every diagnostic span lies inside its
  file, diagnostics render (with and without colours), `run --budget 3` exits with 0 or 1. A mutant is
  compiled as if it were in the directory of its original (so relative `%import`s find the same
  libraries) inside a scratch copy of the corpus; imports that resolve outside it are never read.
- **Generated programs** (`ProgramGen`, `GeneratedFuzzSuite`): well-typed, stratified, terminating
  programs over a small vocabulary — base relations with facts (some `%input`, loaded from a facts file),
  derived relations in strata with recursion, negation, aggregates (with disjunctions inside), comparisons,
  disjunctions, arithmetic, a user enumeration, a constructor type, the prelude families `option` and
  `list`, `len`, and a counter with `%terminates`. Properties: the compiler accepts them; the semi-naive
  engine agrees on every relation with a naive reference evaluator of the core program
  (`NaiveEvaluator`: Definition 8.7 with structural words, no deltas, no indexes); the output does not
  change when the items are permuted, an unused relation is added or relations are renamed; adding
  `%mode` (the demand transformation) does not change query answers; and the robustness properties above
  hold, with "accepted programs run to completion" in addition. Shrinking removes rules and facts.

Every compilation and run happens on a thread with a time limit (20 s); the engine stops at its next
round when interrupted. Failing programs (after shrinking) are written to `target/fuzz-failures/<suite>/`
together with the problem and the seed.

```
sbt test                                                    # short run: 100–150 tests per property, fixed seed
sbt fuzz                                                    # long run: 2000 tests per property, random seed
HUGIN_FUZZ_COUNT=10000 HUGIN_FUZZ_SEED=42 sbt fuzz          # more tests, a given seed
```

The long run prints its seed (`MutationFuzzSuite: 2000 tests per property, seed …`). To reproduce a
failure, rerun with that seed and the same count (`HUGIN_FUZZ_SEED=<seed> HUGIN_FUZZ_COUNT=<n> sbt fuzz`),
or rerun only the failing case with the `Failing seed` that munit prints:
`HUGIN_FUZZ_SEED=<failing seed> HUGIN_FUZZ_COUNT=1 sbt "testOnly hugin.fuzz.GeneratedFuzzSuite"`. A bug
that is fixed gets a golden test in `tests/` (e.g. `tests/run/f_repeated_variable.hgn`, found by the
differential test). `.github/workflows/fuzz.yml` runs `sbt fuzz` nightly (and on demand, with count and
seed as inputs) and uploads `target/fuzz-failures` as an artifact when it fails.

Known issues the fuzzers found, which the generator avoids until they are resolved:

- A disjunction inside an aggregate whose outer variables are bound only through the recursion
  (`s Y :- s X, Y = X + 1, N = count { V | e V ; p Y V }, …`) is rejected with a stratification cycle
  (E0601) through the demand of its auxiliary relation (see `docs/NOTES.md`, "Disjunction inside
  aggregates"); the generator binds such variables with atoms of earlier relations.

## Continuous integration and formatting

`.github/workflows/ci.yml` runs on every push and pull request:

- **Formatting** — `sbt scalafmtCheckAll scalafmtSbtCheck` (configuration in `.scalafmt.conf`).
- **Build and test** on JDK 17 and 21 — compilation with warnings as errors (`CI` set in the
  environment enables `-Werror`, see `build.sbt`), the golden test suite (`sbt test`), and
  `scripts/smoke.sh`, which runs every example through the `bin/hugin` launcher and checks that
  `hugin lsp` answers `initialize`.
- **VS Code extension** — `npm ci` and `vsce package` in `editors/vscode`; the `.vsix` is uploaded as the
  artifact `hugin-vscode`.

`.github/workflows/fuzz.yml` runs the long fuzz run nightly (see "Fuzz testing").

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
