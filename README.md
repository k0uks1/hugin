# Hugin — reference implementation

A reference implementation of **Hugin**, the two-level typed Datalog with first-class facts described in
*Hugin: A Two-Level Typed Datalog with First-Class Facts — Formal Language Definition (Draft, revision 7)*.

It implements the whole pipeline of the definition: parsing, the meta level of the redesign (a
dependently typed two-level type theory elaborated by normalisation by evaluation, with modules,
functors, formula functions, families of object constants and functions defined by clauses), staging into
a monomorphic object program, object-level typing and moding, object-level elaboration (records,
disjunction, demand transformation, derivations), the stratification / completeness / termination checks, compilation to the core IR of
Section 9.3, and a semi-naive interpreter over an interning store. An efficient Datalog engine is out of
scope; the interpreter is meant to make programs runnable and results comparable.

> **Redesign in progress.** The language is moving to a Datalog∃! object level (every constructor a
> fact, termination by size-change, bound arithmetic columns) under a total, dependently typed meta
> level in clause syntax, where directives such as `%demand`/`%mode` are meta functions. The meta level
> (Phase B) is done; see `docs/REDESIGN.md` for the decisions and the implementation plan.

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

### Bound columns

The last column of a relation can be a **bound column** `min τ` or `max τ` (`τ` an integer type, Limit
Datalog): the relation keeps the best value per key, so recursion through arithmetic terminates where
nothing decreases. Values that would improve forever become `-∞` (`min`) or `∞` (`max`):

```
dist : (v : node) -> (d : min int) -> rel.
dist S 0 :- source S.
dist W (D + C) :- dist V D, edge V W C.     (* a negative cycle gives `dist v (-∞)` *)
```

Rules that read a bound column of their own recursive component must be type-consistent (E0606): the
value occurs linearly, only in the head's bound column and in `<`/`<=`/`>`/`>=` comparisons, in the
direction in which improving it improves the head. Misplaced bound columns are E0605. See
`docs/REDESIGN.md` §5.2 and `docs/NOTES.md`, "Bound columns".

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
hugin fix <file.hgn>      apply the machine-applicable suggestions to the file, until none is left
hugin phases              list the compiler phases
hugin explain <code>      explain a diagnostic code (e.g. E0401); --list lists all codes and lints
hugin query <file.hgn> <request> [<line>:<col>]
                          ask the compiler: hover, definition, references, completions
                          (at a position), symbols, diagnostics
hugin repl [<file.hgn> ...]
                          an interactive session, starting with these files (see below)
hugin lsp                 run the language server (LSP over stdin/stdout) for editors

  --facts <file>          load ground facts for input relations (repeatable)
  --print-after <phase>,… print the program after these phases (`all` for every phase)
  --stop-after <phase>    stop compilation after this phase
  --stats                 print compiler phase timings and evaluation statistics
  --all-relations         print the facts of every relation (including fact constructors and demand relations)
  --color / --no-color    colour diagnostics
  --error-format human|json
                          rendered diagnostics (default) or JSON lines
  -W, --warn <lint>       report the lint as a warning (repeatable, as are -A and -D)
  -A, --allow <lint>      allow the lint: do not report it
  -D, --deny <lint>       deny the lint: report it as an error
  --deny-warnings         report every lint without a flag that warns by default as an error
  --explain-termination   print the termination argument of every recursive component
  --no-prelude            do not include the standard prelude
```

### Lints and fixes

Every warning is a named *lint* (`hugin explain --list` shows the names next to the `W` codes):
`undefined_constant_expressions` (W0001), `singleton_variables` (W0002), `unused_definitions` (W0003),
`empty_formula_functions` (W0005), `unreachable_clauses` (W0006). A lint is given by its name or its code;
the last flag for a lint wins, and an explicit `-W` keeps a lint a warning under `--deny-warnings`. A denied
lint is reported as an error (`error[W0002]`) and makes the command fail. Each reported lint has a note
saying where its level comes from (`` `-W singleton_variables` is on by default ``). The launcher script
of `sbt stage` passes arguments starting with `-D` to the JVM, so with it write `--deny <lint>`.

`hugin fix FILE` applies the suggestions marked machine-applicable (adding a missing `.`, replacing a
singleton variable by `_`, adding missing labels as `_`, `%complete`, `%fact`, a missing `%mode`, the
binders of a declared type as parameters of the definition) whose edits lie in the file, recompiling after each round until none is left, as `cargo fix`
does. Suggestions that are guesses (a similar name) are only shown, and lints at `-A` are not fixed.

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
  | `:stats on\|off` | evaluation statistics |
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
program without queries and outputs prints all plain, non-input relations. There are no round budgets
(the `Cut` rule of Section 9.7 and `%partial` were removed): every accepted program terminates
(docs/REDESIGN.md §4.6).

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
| `elaborate` | REDESIGN §6 | loads the prelude and every `%import`ed file (missing and cyclic imports); bidirectional elaboration of the meta level (`hugin.core`): names, dependent types, stage inference (inserts quotes `⟨·⟩`, splices `$·`, lifts `⇑`), implicit arguments by pattern unification, inferred universe levels, functions by clauses with coverage and size-change termination, modules and signatures, families of object constants |
| `stage` | REDESIGN §6.9 | normalises the object items, which runs the meta code they splice: module bodies are instantiated with fresh object constants (`roads.path`), formula functions expanded hygienically, families instantiated at closed arguments (`len[int]`; generic rules per instance, polymorphic recursion rejected); hands the object program over to the object level |
| `directives` | Fig. 2 | attaches `%mode %terminates %open %input %output %derivations %name` to relations |
| `constFold` | 3.3 | folds literal arithmetic (Prop. 3.1); undefined folds are warnings (the rule never fires) |
| `objTyper` | 5, 6.1, 6.2 | well-formed declarations, subtyping/members, best typing contexts by meets, subsumption checks, projections/updates/joins, ascriptions as checked downcasts |
| `moding` | 6.3 | binding steps, canonical (greedy) order, range restriction for every mode, applicable modes of calls |
| `records` | 7.1 | projections `X.l` and updates `(X with {...})` on closed types → one rule per member |
| `disjunction` | 7.2 | splits disjunctions and multi-head rules |
| `demand` | 7.3 | guards and propagation rules (`typed^d[++-]`) for moded relations |
| `derivations` | 7.4 | derivation relations `@r` / `@r#i` |
| `stratify` | 6.4 | dependency graph, strongly connected components in dependency order, negative cycles (reported with the cycle) |
| `bound-columns` | — | bound columns are last integer columns of unmoded relations (E0605); rules over bound columns of their own component are type-consistent (E0606) |
| `completeness` | 6.5 | incompleteness propagation and Definition 6.6 (also for queries) |
| `termination` | 10 | constructive rules, growing components; size-change termination without annotations: descent along derivations (A) and guarded induction (B) with an inferred or `%terminates`-declared measure (interval reasoning, lexicographic measures, mutual recursion; see `docs/NOTES.md`) |
| `lower` | 9.3 | compiles core rules to `Scan / Deref / Tag / Eval / Test / Lookup / NotIn / Agg` and `Make / Insert` over registers |

The runtime (`hugin.runtime`) implements Section 9: words are literals or identities `(c, n)`; every
relation is an array of tuples with an interning map and hash indexes on bound columns; components are
evaluated in order by semi-naive iteration with old/delta/full windows (Section 9.5); components with
queries run over the final store. A relation with a bound
column keeps one current tuple per key (a better value is appended, the old tuple becomes invisible, so
the windows stay identity ranges and the delta holds the improved keys); components with bound columns
check the value propagation graph for positive cycles after rounds 4, 8, 16, … and set the values on and
after them to `∞` (`runtime/Divergence.scala`).

Source layout:

```
src/main/resources/hugin/stdlib/prelude.hgn   the prelude
src/main/scala/hugin/
  util/            sources, slices and spans, rustc-style diagnostics, error-code catalog, graph algorithms (JGraphT)
  syntax/          lexer, parser (ParserPhase), surface trees, printer, generic tree operations (TreeOps),
                   item slices of a file (Slices)
  compiler/        Settings and Display, CompilationUnit, Context, Phase / MiniPhase / MegaPhase, the phase
                   plan, libraries (the prelude and imported files, the import graph), the semantic index for
                   tooling (SemanticIndex)
  core/            the meta level (docs/REDESIGN.md Phase B): core syntax and values, normalisation by
                   evaluation, pattern unification, universe levels, families and modules, staging, the
                   elaboration of a program in parts (ProgramElab, MetaLevel); core/elab/ is the
                   bidirectional elaborator (one trait per concern, mixed into Elaborator), core/handover/
                   stages the object items into the object program
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
- `SemanticIndex`, filled by the elaborator, staging and the object typer, records which symbol every name resolves
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

Incrementality is per item for the elaboration: the prelude and the imported files are elaborated as a
chain, each file once per revision of the files before it, shared by the programs whose chains share
it; the items of a program are parsed from their own text; its declarations are elaborated together and
each object item (rule, query, directive) on its own against them, so editing a rule elaborates only that
rule, editing a declaration the declarations and the object items, and moving items nothing. Memos no
recent demand reaches are evicted. Staging and the object-level phases still run on the whole program
after an edit. See `docs/INCREMENTALITY.md` (issue #4).

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

- *staging* (recorded when the object items are staged): object code passed where meta code is expected is
  *quoted* (`p X` passes the code `⟨X⟩` to the formula function `p`), meta code used in object code is
  *spliced* (`I.price < 10` in the body of `cheap` inserts the code bound to `I`), and a compile-time
  primitive in object code is *persisted* as a literal (`X = k` with `k : int = 6 * 7` embeds `42`).
  Code in a functor or a formula function is evaluated once per application; every value is shown.
  The innermost staged piece of code around the position is described;
- *family instances* (recorded when the object items are staged): a use of `cons`, `len` or `list` shows the
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
a line, and the binders of a declared type used in the definition (`f : (x : A) -> B = e.` becomes
`f (x : A) : B = e.`).

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

Diagnostics are collected, never thrown: the parser resynchronises at item boundaries, the elaborator
drops an item at its first error (and does not report the errors that follow from it), and object-level
phases drop ill-formed rules. Every diagnostic
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

The diagnostic classes of Appendix A.1 are all distinguished; every diagnostic is a typed problem with a
code (`src/main/scala/hugin/util/diagnostics/Code.scala`, explained in `docs/errors/<code>.md` and by
`hugin explain <code>`).

## Tests

Three kinds of tests, all run by `sbt test`:

- **Unit suites** (`src/test/scala/hugin/...`, mirroring the main packages): lexer and parser
  (precedence, braces, `%infix`, recovery), tree operations, the meta level (`core`: evaluation,
  unification, universes, inductive families and clauses, elaboration errors, families, modules, formula
  functions, staging and the handover), shared primitive semantics, type operations (subtyping, members, meets), moding,
  stratification, completeness, interval reasoning, lowering, the command-line parser and exit codes,
  rendering of diagnostics,
  differential tests of the engine (random graphs against a naive fixpoint,
  interning, aggregates), the query layer, and the language server (position conversion, the
  request handlers on in-memory documents, and one session over piped streams).
- **Golden tests** in `tests/`, in the style of dotty's test suite:
  - `tests/run/X.hgn` — compiled and run; stdout (and warnings, as `//` lines) must equal `X.check`.
    `X.facts` is loaded as input; `X.flags` holds extra options (e.g. `--explain-termination`).
  - `tests/neg/X.hgn` — must fail; the rendered diagnostics must equal `X.check` (with `X.facts`, the
    failure may come from loading the input). Inline annotations `(*~ E0603 *)` (on the reported line;
    `(*~^ E0603 *)` for the line above) state the codes independently of the wording: a file with
    annotations must account for exactly the diagnostics reported in it.
  - `tests/pos/X.hgn` — must compile without errors.
  - `tests/fix/X.hgn` — `hugin fix` applied to a copy must give `X.fixed`, which must compile without
    errors and be a fixed point (one test per kind of machine-applicable suggestion).
  - `tests/json/X.hgn` — checked with `--error-format=json`; the JSON lines must equal `X.check`.
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
  file, diagnostics render (with and without colours), `run` exits with 0 or 1. A mutant is
  compiled as if it were in the directory of its original (so relative `%import`s find the same
  libraries) inside a scratch copy of the corpus; imports that resolve outside it are never read.
- **Generated programs** (`ProgramGen`, `GeneratedFuzzSuite`): well-typed, stratified, terminating
  programs over a small vocabulary — base relations with facts (some `%input`, loaded from a facts file),
  derived relations in strata with recursion, negation, aggregates (with disjunctions inside), comparisons,
  disjunctions, arithmetic, a user enumeration, a constructor type, the prelude families `option` and
  `list`, `len`, a counter with `%terminates`, and bound columns over a weighted graph (with divergence). Properties: the compiler accepts them; the semi-naive
  engine agrees on every relation with a naive reference evaluator of the core program
  (`NaiveEvaluator`: Definition 8.7 with structural words, no deltas, no indexes; bound columns by Kaminski
  et al.'s Algorithm 1 with Floyd–Warshall every round); the output does not
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
