# IO: reading files and parsing their contents

Design note for [issue #187](https://github.com/k0uks1/hugin/issues/187): where a Hugin program reads
files, how a total, dependently typed meta level can read them and stay sound and deterministic, how the
reads become dependencies of the query database, how their contents are parsed, and what the browser
playground and the safety rules need. Status: research, for the designer's approval before any
implementation. Written against `28dbcb1` (`origin/ccr-48027e29-daam41`). No code was changed or built.

Contents: 1 recommendations, 2 Hugin today, 3 prior art, 4 where IO happens, 5 tracked dependencies,
6 parsing, 7 the playground, 8 safety, 9 worked examples, 10 alternatives rejected, 11 batches, 12 open
decisions, 13 sources.

## 1. Recommendations

1. **Do IO at both levels, with two mechanisms that never make the meta language effectful.**
   - *Run time, for data:* an input relation can name a **source**, a file and a format:
     `%from (csv "edges.csv") edge.` The loader reads the file when the program is evaluated, as the
     facts files are read today, and checks each value against the relation's column types. This is
     Soufflé's `.input` and Nemo's `@import` (3.1), typed by Hugin's declarations.
   - *Compile time, for schemas, configurations, grammars and small tables:* `%import "p" as text` is a
     meta expression whose value is the text of a file, as `%import "p"` is already the module of a
     file. Its path is a **literal**, resolved before elaboration. This is Dhall's `as Text`, Rust's
     `include_str!` and Zig's `@embedFile` (3.2). No `IO` monad, no effect system and no `readFile`
     primitive. The file's text is one more input of the compilation, like a source file. So the meta
     level stays total, and a compilation stays a function of the texts of the files it reads.
2. **Every read goes through `SourceText`.** `SourceText` is already the compiler's only input: programs,
   imported files and facts files (`query/CompilerQueries.scala` 7–11). A data file or text import is one
   more key of it, so the database records it as a dependency, the language server invalidates it like
   a file on disk (`lsp/Features.scala` 54–56), and the playground fills it from a virtual file system.
   A run-time source invalidates only evaluation (`Fixpoint`). A text import invalidates the
   elaboration of the file that imports it, like an import. Large run-time files get a stamp input
   (size, time, hash) instead of their text (5.3).
3. **Built-in formats at run time, a parser library at compile time, grammars for the rest.** The
   loader knows `facts` (today's format), `csv`/`tsv`, `lines`, `chars`, `jsonl`, `json` and `pattern`
   (a regular expression with named groups). It fills the columns by **label** (a CSV header, a JSON
   key or a group name names a column of the relation) or by position. It reports errors with spans
   into the data file, as code E0801 does for facts files today. At compile time, a small
   string-primitive set (`chars`, `codepoint`, `parseInt`, `parseFloat`) makes a parser-combinator
   library `std/parse` possible in total meta code. Grammar-derived relations, the `%regex` showcase
   generalised to context-free grammars over a `chars` input, are a library and not a compiler feature
   (6.3).
4. **Restrict paths by default.** A path is relative, stays inside a *read root* (the main file's
   directory, or `--root`), and does not escape it through `..` or a symbolic link. A library reads, at
   compile time, only files below its own directory, as a Zig module reads only its package's paths
   (3.2). Only the main program attaches run-time sources; a library can declare an input relation, but
   cannot say where its data comes from. `--allow-read=DIR` widens the root, after Deno (3.4).
5. **Eight batches, one PR each** (11): run-time sources with CSV and lines first (R1), then the tools
   (R2), the playground's file system (R3), text imports and string primitives (C1), `std/parse` (C2),
   grammar and pattern parsing (G1), JSON (J1), and object-level string functions only if still needed
   (S1, deferred).

## 2. Hugin today

### 2.1 Run-time input

- `%input r.` and `%open r.` attach the attributes `ainput` and `aopen` (`std/reflect.hgn` 165–190). An
  input relation's facts come from *facts files*: ground facts in Hugin's syntax, given with
  `--facts FILE`, repeatable (`reference/src/object/io.md`, "Input facts"). Loading a fact interns its
  nested constructor terms (`runtime/FactLoader.scala`, 96 lines). Constructor and enumeration values
  are written by name (`a`, `(pair 1 "x")`). Bad facts are reported as E0801 with a span into the facts
  file (`runtime/InputProblems.scala`).
- `syntax/FactReader.scala` (107 lines) is a fast reader for facts files in the common form. It builds
  the same trees as the program parser, which takes over on anything unusual. It was added because
  parsing a 14 161-fact file was 18–24 % of a run (`docs/PERFORMANCE.md`, "shortest_grid"). A loader
  for large inputs must skip trees altogether (6.5).
- `%output r.` chooses the printed relations. There is no output to files.
- The object level's string operations are concatenation `^` and comparison
  (`reference/src/object/arithmetic.md`). There is no substring, length, split or conversion, so a rule
  cannot take a line apart.

### 2.2 Compile time

- `%import "path"` is a meta expression whose value is the module of another file, resolved relative to
  the importing file (`compiler/Libraries.scala` 25–60, `reference/src/modules.md`, "Imports"). The path
  is a literal, so the import graph is known before elaboration (`ImportGraph`). This is already a
  compile-time file read with a static path, tracked by the database: the model 1.1 extends.
- The meta level is total: functions defined by clauses pass the size-change check (E0912,
  `reference/src/meta/termination.md`). It has `int`, `float` and `string` as compile-time values with
  arithmetic and `^`, but **no comparisons** (`reference/src/meta/functions.md`, "Literals and primitive
  operations") and **no way to take a string apart**. Its primitives are `same`, `labels`, `derive`,
  `derived` and `qatom` (`std/reflect.hgn` 102, 198–203; `core/Primitives.scala`). A parser in the meta
  language needs new primitives first (6.2).
- Directives are meta functions. `%regex` (`site/example-regex.hgn`) turns a regular expression into one
  relation per subexpression over `text : (at : int) -> (c : string) -> rel`, with one fact per
  character. It is the existing example of grammar-derived relations. Today its input text is written
  by hand as facts.

### 2.3 Tools

| client | how it reads files today |
|---|---|
| CLI (`cli/Main.scala`) | `hugin run p.hgn --facts f.facts`; facts files are checked to exist, then `Evaluate` reads them through `SourceText` (`FactsFile`, `query/EvaluationQueries.scala` 18–21) |
| REPL (`repl/Session.scala`) | `:facts FILE`, `:reload` rereads loaded programs, facts files and imports |
| LSP (`lsp/`) | open documents are set into `SourceText`; `didChangeWatchedFiles` removes a closed file's text so it is read again; the VS Code client watches only `**/*.{hgn,facts}` (`editors/vscode/extension.js` 51); `.facts` files get syntax diagnostics only |
| playground (`web/`, `site/play/worker.js`) | `JsSourceFiles.readFile` is always `None`: one file, `std/` imports only, no facts. Reference examples with a facts block are left out (`site/examples.mjs` 3, 28) |

The platform interface `util/SourceFiles.scala` (30 lines) is the only place where the compiler touches
the file system. `platform/Platform.scala` (JVM) and `web/.../platform/Platform.scala` (Scala.js)
implement it.

## 3. Prior art

### 3.1 Run-time input in Datalog engines

- **Soufflé.** `.input r(IO=file, filename="…", delimiter=",", headers=true, rfc4180=true,
  columns="2:0")` and `.output`. The IO types are `file`, `stdin` and `sqlite`, and the source also
  registers `json` and `jsonfile` readers and writers (`IOSystem.h`, `ReadStreamJSON.h`). The default
  input is `<relation>.facts`, tab-separated, below `-F`. Input is read by a dedicated reader
  (`ReadStreamCSV`), not the Datalog parser. Its errors are line-based: "Error converting <x> in column
  3 in line 7", "Values missing in line 7". Strings are taken apart at run time with functors (`substr`,
  `strlen`, `to_number`, `cat`, `contains`, `match`) and C++ user-defined functors loaded at evaluation
  time.
- **Nemo** (TU Dresden). `@import people :- csv { resource = "data/people.csv", format = (string, int,
  skip) }.` with `csv`, `dsv`, `tsv`, the RDF formats, `sparql` and `json`. JSON becomes triples over
  object IDs. Parameters are `limit`, `compression`, `ignore_headers` and `quoting`, plus HTTP headers.
  Notably, **lines that do not match the declared format are skipped silently**.
- **Datomic.** A query's `:in` clause binds inputs. A relation binding `[[?a ?b]]` takes any collection
  of tuples, so data read by the host program is queried directly. IO stays in the host language.
- **LogicBlox** loaded delimited files through its TDX ("tabular data exchange") services, which map
  file columns to predicates outside the logic program (Aref et al. 2015). Like Datomic, it keeps
  formats outside the language.
- **Program analysis** (Doop, CodeQL): a separate *extractor* parses the analysed sources into facts,
  and the Datalog program reads only facts. This is the realistic route for "source code to analyse":
  Hugin should read facts that an extractor produced, not parse Java.

**Lessons:** run-time input is a per-relation declaration of a file and a format, with types from the
schema. A fast dedicated reader beats the language parser. Error reports must give file positions;
Nemo's silent skipping is a trap that Hugin should not copy (12, decision 7).

### 3.2 Compile-time IO in staged and dependently typed languages

- **Template Haskell.** `runIO :: IO a -> Q a` runs arbitrary IO in a splice. The documentation warns
  that the order of splices is not guaranteed. `addDependentFile :: FilePath -> Q ()` must be called
  *by hand*. It records a file "so the compiler can recognize that it should re-compile the Haskell file
  when an external file changes", based on content, not modification time; `ghc -M` does not know
  these dependencies. Forgetting the call gives stale builds; Safe Haskell forbids TH.
- **Lean 4.** Elaborators run in `CoreM`/`MetaM`, which can lift `IO`, so a macro can read any file.
  `include_str "file"` inserts a file's text as a string literal. Lake did not know that dependency
  (lean4#2762, moved from lake#86), and the fix was a manual `needs` option on libraries (closed by
  lean4#7703 in April 2025). A maintainer objected that dependencies recorded *during* elaboration come
  too late for Lake, which must decide what to rebuild *before* elaborating.
  `compile_time_search_path%` is documented as unsafe on another machine.
- **Rust.** `include_str!("f")` gives a `&'static str`, relative to the current file; rustc tracks the
  file for incremental rebuilds. Build scripts (`build.rs`) run arbitrary code before compilation and
  declare `cargo::rerun-if-changed=PATH`. Without it, Cargo reruns the script whenever *any* file in
  the package changes. Generated files go to `OUT_DIR`. Procedural macros run unsandboxed.
- **F# type providers.** A type provider generates types at design time from a static argument, a
  sample file or a URL. `CsvProvider<"data/MSFT.csv">` infers the columns' names from the header and
  their types from the rows. This is the model of "a schema from a file at compile time" (4.3).
- **Idris 2 elaborator reflection.** `Elab` has `readFile : LookupDir -> String -> Elab (Maybe String)`
  and `idrisDir : LookupDir -> Elab String`. A file is read relative to a project directory chosen by an
  enumeration, not an arbitrary path.
- **Racket.** `include` inlines the syntax of a file and calls `register-external-file`
  (`compiler/cm-accomplice`). The compilation manager records the path in the module's `.dep` file and
  recompiles when it changes. Any macro can call the same hook: a dependency is a log message, recorded
  dynamically.
- **Zig.** `@embedFile(comptime path)` returns the file's bytes "equivalent to a string literal with the
  file contents"; the path is comptime-known and resolved like `@import`. The build system restricts
  embedding to the files a module may see: its root directory, its package's `.paths`, or files
  registered with `addAnonymousImport`.
- **Dhall**, a total configuration language with imports, is the closest relative of Hugin's meta
  level. Its imports are resolved strictly, even unused ones, and **computed imports are forbidden**, so
  a path never depends on a value. `./file as Text` imports a file's text. An import may carry a
  `sha256:` integrity check over its normal form, and such an import is cached forever. A remote import
  **cannot import local files or environment variables**. Type checking always terminates, and a
  well-typed expression always evaluates.

**Lessons:** static (literal) paths make dependencies known before elaboration, which Lean and TH lack
and had to patch. Hugin's query database records dependencies *during* computation (salsa style, unlike
Lake), so a dynamic path would still be tracked. But static paths are also what makes the safety rules
checkable, the playground's file set known, and the LSP's watch list exact. Confinement to a package
directory (Zig, Idris) and "remote code cannot read local files" (Dhall) are the precedents for
libraries.

### 3.3 Effects in total languages

- **Agda** has no effects in the type theory. `IO` is a postulated type (`Agda.Builtin.IO`), and the
  operations are `postulate`s bound to Haskell with `{-# COMPILE GHC … #-}`. Type checking never runs
  them; only compiled code does. `--safe` forbids postulates.
- **Idris 1's `Effects` library** (Brady 2013) indexes computations by the algebraic effects they may
  perform, with handlers per context. Idris 2 runs `IO` only at run time; at compile time it offers only
  `Elab`'s confined `readFile`.
- **Koka** tracks effects in row-polymorphic types: `total`, `exn`, `div` (may diverge), `console` and
  `ndet`. Totality itself is an effect: a function without `div` in its type terminates.

**Lessons:** total languages keep the reasoning level pure and push IO to run time (Agda), or confine
compile-time IO to a narrow, typed capability (Idris 2). An effect system à la Koka would add a type
discipline, effect rows, to a meta level whose only reason to perform IO is reading a few files. The
narrow capability is enough.

### 3.4 Permissions

**Deno** is sandboxed by default. `--allow-read=./data` limits reads to one directory, and a refused
operation throws `NotCapable`. Statically analysable imports are loaded without `--allow-read`, but a
computed `import()` is checked at run time.

## 4. Where IO happens

### 4.1 The two stages of a Hugin run

`hugin run` compiles and then evaluates in one process, but the two stages differ in what a file read
can change:

| | compile time (meta) | run time (object) |
|---|---|---|
| can change | declarations, rules, types, generated relations | only the facts of input relations |
| invalidates | elaboration of the importing file and everything after it | `Fixpoint` and `Evaluate` only |
| speed | meta interpreter (lists of strings) | dedicated loader into `Store` |
| suits | schemas, configurations, grammars, small tables, embedded text | data: edges, logs, measurements, extractor output |
| precedent | Dhall `as Text`, `include_str!`, `@embedFile`, type providers | Soufflé `.input`, Nemo `@import` |

Both are needed: data belongs at run time, where it does not cost elaboration and the program can be
rerun on other data. Structure that depends on a file (a relation per CSV column, rules from a
grammar file) can only come from compile time.

### 4.2 Run time: sources on input relations

A new attribute and a new local directive in `std/reflect` (or a module `std/io`, decision 2):

```text
source : Type.
facts : string -> source.                 (* today's facts files *)
csv, tsv, lines, chars, jsonl, json : string -> source.
pattern : string -> string -> source.     (* file, regular expression with named groups *)
headed, skipInvalid : source -> source.   (* options *)
asource : source -> attr.
from : source -> decl -> decl.
from S D = attach (asource S) (input D).
```

`%from (csv "edges.csv") edge.` and the prefix form `%from (lines "app.log") line : … -> rel.` make the
relation an input relation whose facts come from the file, plus any `--facts` files and rules, as for
`%input` today. `%open` still makes it incomplete. The attribute is data computed by total meta code,
so a source can come from a library function (`%from (dataset "q3")`). Its path is resolved after
elaboration, relative to the file that wrote the directive, and checked by the rules of 8. The path is
known when the program is compiled, before evaluation, so the evaluation's file set is known before any
file is read.

The CLI keeps `--facts FILE`. A new option `--input r=FILE` replaces the file of the source of `r`, so
the same program runs on other data (Soufflé's `-F`).

### 4.3 Compile time: text imports

```text
Import ::= "%import" STRING ("as" ("text" | "lines" | "source"))?
```

- `%import "f" as text : string` is the file's text (UTF-8, line ends kept);
- `as lines : list string` is its lines;
- `as source : src` is an opaque value with `text : src -> string`, for parsers that report errors in the
  file (6.4).

The path is a literal, resolved like an import, and part of the import graph, so a missing file is
E0108 and the file set is known before elaboration. The file is read once per compilation and text.
**Determinism:** a compilation is a function of the texts of the files it reads, which is already true
of source files. **Totality:** reading a known file terminates, and the meta level performs no effect,
because the value is a constant of the program, like a string literal written in the source. Nothing
in the termination checker or the evaluator changes. Errors are a missing file (E0108), invalid UTF-8,
or a file over a size cap (a new code; 1 MiB by default, see 6.5).

A type-provider pattern follows: a directive receives the text and generates items. Today, though, an
additive directive can declare only derived relations (`irelation (derive r "l") cols`, columns copied
from existing constants; `reference/src/reflection.md`, "Symbols and derived constants"). A provider that
declares a relation with a column per header field needs a way to make columns of base types (open
decision 10). Until then, the program declares the relation and the compile-time code fills it with
facts (9.1, variant B).

### 4.4 Why not an IO monad or effects in the meta language

- An `IO` type in the meta language (TH's `runIO`, Lean's `MetaM`) makes every elaboration potentially
  nondeterministic and dependent on files no one declared. It needs a dependency hook that users
  forget (TH, Lean before `needs`). It also breaks the playground, which has no file system, and the
  language server, which elaborates on every keystroke.
- A `readFile : string -> option string` primitive over a snapshot of the file system would be pure and
  tracked: the database records each `SourceText` read. But the path is computed, so the safety rules
  can be checked only at evaluation, the LSP cannot know what to watch before elaborating, and the
  playground cannot know which files to ship. It can be added later on top of static imports if a need
  appears (decision 3).
- An effect system (Koka, Idris `Effects`) is a large type-system feature for one effect.

## 5. Tracked dependencies

### 5.1 The queries

The database (`query/Database.scala`) records every `Input` and `Query` that a computation reads.
`SourceText` already serves programs, imports and facts files. New keys and queries:

| query | key | reads | read by |
|---|---|---|---|
| `SourceText` (exists) | path | the file, the editor's buffer or the playground's file | everything |
| `FileStamp` (new input) | path | size, modification time, content hash; for run-time files over a threshold | `DataTable` |
| `TextImport` (new) | resolved path, mode | `SourceText` | elaboration of the importing file |
| `DataTable` (new; generalises `FactsFile`) | path, format, the relation's column layout | `SourceText` or `FileStamp`, then the file | `Fixpoint` |
| `Sources` (new) | `CompileKey` | `Lowered`: the sources of the input relations, resolved | `Fixpoint`, the LSP's watch list |

A text import is resolved in `FileImports`/`ImportGraph`, so the import chain (`ElabLibrary`) depends on
it as on an imported file: editing the CSV re-elaborates the file that imports it, and early cut-off
stops at the first unchanged result. `DataTable` is keyed by the column layout and not the whole
program, so editing a rule does not reparse a data file. This is `FactsFile`'s "once per text"
generalised. `Fixpoint` already takes the facts files' parses as inputs
(`query/EvaluationQueries.scala` 23–41). The REPL's reuse of the fixpoint (incrementality-2 PR 3) carries
over: a changed data file reruns `Fixpoint`, and a changed rule reuses the parsed tables.

### 5.2 The language server and the REPL

- The LSP publishes, per document, the files its compilation read (`Sources` plus text imports) and
  registers watchers for them dynamically (`client/registerCapability`, `workspace/didChangeWatchedFiles`
  with the exact paths). The VS Code client's static glob covers only `.hgn` and `.facts`, so a `.csv`
  edit is not seen today. `changedOnDisk` already handles the event.
- A data file open in the editor is an ordinary document: its buffer is `SourceText`, so typing in the
  CSV re-evaluates on the next run. Diagnostics of a data file (E0801 and its successors) are published
  on that file, as `.facts` files get syntax diagnostics today.
- Hover on the path in `%from (csv "edges.csv")` shows the resolved path and the row count. Go to
  definition opens the file.
- REPL: `:reload` rereads sources and text imports. `:input r FILE` is the session form of `--input`.

### 5.3 Large files

`SourceText` holds a file's text as a string, and the database compares inputs by value. For a 500 MB
CSV that is twice the memory and a slow comparison. Run-time files above a threshold (say 4 MiB) are
represented by a `FileStamp` (size, time, and a hash computed only when size and time are ambiguous,
the "racily clean" problem of git and make). `DataTable` streams the file and keeps only the columnar
table. TH bases dependencies on content, Cargo on modification time, and the stamp combines them. An
open editor buffer is always text. Text imports are capped (6.5), so they never need a stamp.

## 6. Parsing

### 6.1 Built-in run-time formats

| format | relation shape | rule |
|---|---|---|
| `facts` | any input relation | today's facts-file syntax (`FactReader` then the parser) |
| `csv`, `tsv` | columns of base types, refinements, or open/enumeration types | RFC 4180 quoting; with `headed`, the header names the columns by **label**, otherwise positional; a cell for an open type is a constant's name or a facts-syntax term |
| `lines` | `(line : int) -> (text : string) -> rel`, or `(text : string) -> rel` | one fact per line, numbered from 1 |
| `chars` | `(at : int) -> (c : string) -> rel` | one fact per code point: the input of `%regex` and grammars (6.3) |
| `pattern` | labelled columns | a regular expression per line; each named group fills the column with its label; an optional `line` column gets the line number |
| `jsonl` | labelled columns | one JSON object per line; keys fill columns by label; numbers, strings, booleans (a `bool` enumeration), `null` only in an `option` column |
| `json` | the types of `std/json` | the whole document as a tree of constructor terms: `jnull`, `jbool`, `jnum`, `jstr`, `jarr (list json)`, `jobj (list member)`; rules project it |

Labels are already part of relation types (`(from : int) -> (to : int) -> rel`) and readable by meta
code (`labels : sym -> list string`), so matching by label needs no new syntax. A directive can even
check a header or a pattern's group names against the labels at compile time. Hugin's first-class facts
make `json` natural: a nested document is a constructor term, as nested lists are today, so no triple
encoding is needed (Nemo).

### 6.2 Compile time: a parser library in the meta language

The meta level needs primitives first. They are total, deterministic, and cost a line each in
`core/Primitives.scala`:

| primitive | meaning |
|---|---|
| `chars : string -> list string` | the code points, each as a one-character string |
| `codepoint : string -> int` | the code point of a one-character string (stuck otherwise) |
| `fromCodepoint : int -> string` | the inverse |
| `parseInt : string -> option int`, `parseFloat : string -> option float` | decimal literals |
| `less : A -> A -> bool` | the order of literals (ints, floats, strings by code points), like the object level's |
| `strlen : string -> int` | the number of code points |

With `chars`, a parser consumes a `list string`, and recursion on the remaining input is structural, so
the size-change check accepts the combinators. The one hard case is `many p`: it terminates only if `p`
consumes. `std/parse` can define `many` by recursion on the input with a check that `p` made progress,
returning failure otherwise, as Parsec rejects `many` of a parser that accepts the empty string at run
time. Or it can take fuel, the input's length as a `nat`. Both are accepted by size change. The library
is ordinary Hugin:

```text
parser : Type -> Type.
parser A = list string -> result A.     (* result: ok A rest pos | fail msg pos *)
char, satisfy, many, sepBy, token, int, quoted, …
```

Positions are offsets in code points, counted by the combinators. Cost: the meta interpreter allocates a
cons per character and evaluates closures per combinator step. Hugin has no measurement of it on large
texts. The estimate is 10⁴–10⁵ characters per second, enough for a configuration or a grammar file and
not for data. The cap of 4.3 holds the line (6.5).

### 6.3 Grammar-derived relations

The `%regex` example shows the staged alternative: meta code compiles a grammar into Datalog rules over
`text I C`, and evaluation parses. With the `chars` format, the text comes from a file:

```text
text : (at : int) -> (c : string) -> rel.
%from (chars "input.txt") text.
%regex m pattern.
```

A context-free grammar compiles the same way. This is parsing as deduction (Shieber, Schabes, Pereira
1995): one relation per nonterminal, `n I J` when the text from `I` to `J` derives `n`. It is
CYK/Earley-like and cubic in the worst case, with the parse forest as derivation facts
(`%derivations`). It fits small structured inputs and grammar experiments, and shows off the staging.
It does not fit megabytes: a fact per character costs about 50–100 bytes in the store. `std/grammar`
is a library on top of R1 (`chars`) and needs no compiler work. The `pattern` format covers the common
case, line-oriented logs, in the loader at native speed.

### 6.4 Error positions

- **Run time:** the loader holds the file as a `SourceFile` (`SourceFile.virtual(path, text)`, as
  `FactsFile` does), so every error has a span: an unparsable cell, the wrong number of fields, a value
  of the wrong type, an unknown constant, or a line that does not match the pattern. The span gives
  line and column in the data file, and diagnostics render as for source files. E0801 is extended or
  split (E0802 malformed record, E0803 value does not fit the column; decision for the batch). The
  default is to fail the run after up to 20 errors. `skipInvalid` skips the bad records instead and
  reports a warning with the count; Nemo's silent skipping is rejected.
- **Compile time:** a parser in meta code returns an offset. A primitive item
  `ierrorAt : src -> int -> int -> string -> item` reports a diagnostic at an offset range of the file
  of a `src` (from `%import … as source`), with a note "imported by …" at the import. `src` is opaque,
  so meta code cannot make a span point into a file it did not import.

### 6.5 Performance on large inputs

- **Run time:** the CSV, `lines`, `pattern` and `jsonl` readers parse straight into the columns and
  intern into `Store` without building `Trees`, the lesson of `FactReader`. Strings are interned once
  per distinct value. The target is ≥ 1 M rows/s for a two-integer CSV on the JVM, and a benchmark in
  `bench/` against the same data as facts. `DataTable` memoises per text or stamp, so reruns with
  changed rules do not reparse. Gzip input (Soufflé, Nemo) is cheap on the JVM (`GZIPInputStream`) and
  can wait.
- **Compile time:** a text import is capped at 1 MiB by default (`--max-import-size`). Over the cap,
  the diagnostic suggests a run-time source. This prevents an accidental 100 MB `as text` from hanging
  the editor.
- **Playground:** Scala.js strings and the same loader; files limited by the browser, a 10 MB
  soft cap in the UI.

## 7. The browser playground

### 7.1 A virtual file system

The playground needs no new compiler interface: `SourceText` is the only input, and the worker's
`Session` already sets it for the program (`web/.../Session.scala`). The request gets a `files` field,
`{ "edges.csv": "1,2\n2,3\n" }`, and the session sets each into `SourceText` under the program's
directory. `JsSourceFiles.readFile` stays `None`, so a file that was not supplied is "cannot find". The
same database persists across requests, so an unchanged data file costs nothing.

UI: tabs above the editor (the program first, then data files), a "+" to add an empty file or upload one
(the File API reads it in the page and posts the text), and rename and delete. The data file tab gets
plain-text editing with line numbers. Diagnostics of a data file show in its tab and jump to it.
Sharing: the `#code=` fragment (`site/play/share.js`) becomes a deflated JSON of all files when there is
more than one, so old links keep working. Large shared data makes long URLs, so the UI warns above
~32 KB compressed.

### 7.2 How examples ship data files

- **Reference:** a code block `` ```file edges.csv `` after a `hugin,run` block supplies a file, as
  `` ```facts `` supplies facts today. `ReferenceExamplesSuite` writes these files next to the program
  in a temporary directory. `site/examples.mjs` stops excluding examples with facts or data: a facts
  block becomes a file `main.facts` passed as `--facts`, and the examples appear in the playground with
  their tabs.
- **Landing page and `examples/`:** an example is a directory (`examples/reach/main.hgn`,
  `examples/reach/edges.csv`). The site build bundles the directory into the example's JSON, as
  `typechecker.facts` would be.
- **Size:** examples ship small data (≤ 50 KB). A larger demonstration links to a file that the page
  fetches from the site's own origin on demand.

## 8. Safety

1. **Paths.** A path in a source or a text import is relative and `/`-separated. It is resolved against
   the directory of the file that wrote it and normalised. The result must lie under a read root, after
   resolving symbolic links (`toRealPath`). Absolute paths, `..` escapes, NUL characters and other
   invalid paths are a compile-time error, a new code with the path and the root. `std/` paths are the
   bundled library, as for imports.
2. **Roots.** The default root is the directory of the main program file (the REPL: the current
   directory; the LSP: the workspace folder). `--root DIR` changes it; `--allow-read=DIR` (repeatable)
   adds roots, after Deno. `--allow-read` with no value allows everything, for scripts that read
   `/var/log`. `-` (stdin) is a source only on the command line (`--input r=-`), never in a program.
3. **Libraries.** An imported file reads at compile time only below its own directory, as Zig limits
   `@embedFile` to a module's paths and Idris resolves `readFile` against a project directory. So a
   library ships its own data (a grammar, a table of units), and a dependency cannot read `~/.ssh` at
   compile time. The bundled standard library reads only bundled resources.
4. **Run-time sources belong to the program.** A `%from` attribute is honoured only if the directive is
   in the main program, or in a file under a root the program names with `--allow-read`. A library that
   wants data declares an input relation (`%input r` or `%open r`, a `%complete` requirement in a
   signature), and the program connects it: `%from (csv "x.csv") lib.r.` Local directives in a library
   apply to its own constants (`reference/src/directives.md`, "Local directives"), so this is a check on
   where the directive was written. This is Dhall's "remote code cannot read local files", applied to
   imported code.
5. **No writes, no network, no environment.** Reading is the only capability, and only of regular files.
   Output to files (Soufflé's `.output`) and HTTP sources (Nemo) are out of scope. They would need their
   own permission flags.
6. **Reproducibility.** `hugin run --stats` lists the files read with their hashes. An optional integrity
   check, `%import "grammar.txt" as text sha256 "…"` after Dhall, can come later (decision 9).

## 9. Worked examples (hypothetical syntax)

### 9.1 Reachability over a CSV of edges

`edges.csv`:

```text
from,to
a,b
b,c
c,a
d,e
```

**A: at run time** (recommended for data):

```text
%use "std/io".
edge : (from : string) -> (to : string) -> rel.
%from (headed (csv "edges.csv")) edge.

reach : (from : string) -> (to : string) -> rel.
reach X Y :- edge X Y.
reach X Z :- edge X Y, reach Y Z.
?- reach "a" X.
```

```text
?- reach "a" X.
X = "a".
X = "b".
X = "c".
```

`hugin run reach.hgn --input edge=other.csv` runs it on other data. A malformed row, such as `c,a,x` on
line 4, is reported as `edges.csv:4:5: error[E0802]: the record has 3 fields, but edge has 2 columns`.
With an enumeration `node : type. a, b, c, d, e : node.` and `edge : (from : node) -> (to : node) -> rel`,
the cells are constant names, and `f` would be E0801 "unknown constant `f`" at its cell.

**B: at compile time** (for a small, fixed table; the facts become part of the program):

```text
%use "std/parse".
edge : (from : string) -> (to : string) -> rel.
rows : list (list string) = csvRows (%import "edges.csv" as text).

asFacts : list (list string) -> list item.
asFacts [] = [].
asFacts ([A, B] :: Rest) = '( edge $A $B. ) :: asFacts Rest.
asFacts (_ :: Rest) = ierror "a row needs two fields" :: asFacts Rest.
$asFacts (drop 1 rows).
```

Editing `edges.csv` re-elaborates this file (`TextImport` → the chain), whereas in A it only reruns
`Fixpoint`.

### 9.2 A small log format into typed facts

`app.log`:

```text
2026-10-01T12:00:03 INFO  auth  user=ann login
2026-10-01T12:00:09 ERROR db    timeout after 30s
2026-10-01T12:00:12 WARN  auth  user=bob retry
```

**A: run time, with `pattern`:**

```text
%use "std/io".
level : type. info, warn, error : level.
entry : (line : int) -> (time : string) -> (level : string) -> (component : string) -> (message : string) -> rel.
%from (pattern "app.log" "(?<time>\\S+) (?<level>[A-Z]+) +(?<component>\\w+) +(?<message>.*)") entry.

severity : string -> level -> rel.
severity "INFO" info. severity "WARN" warn. severity "ERROR" error.

event : (line : int) -> (component : string) -> (level : level) -> rel.
event N C L :- entry N _ S C _, severity S L.
unknown_level : (line : int) -> (text : string) -> rel.
unknown_level N S :- entry N _ S _ _, not severity S _.
?- event N C error.
```

```text
?- event N C error.
N = 2, C = "db".
```

At compile time, `%from` can check that the group names `time`, `level`, `component` and `message` are
labels of `entry`. A line that does not match is `app.log:7:1: error[E0802]: the line does not match the
pattern of entry`.

**B: compile time, with `std/parse`** (for a log shipped with the program, such as a fixture): the parser
returns typed values and points errors into the file.

```text
%use "std/parse".
log : src = %import "app.log" as source.
lvl : parser term = choice [kw "INFO" '( info ), kw "WARN" '( warn ), kw "ERROR" '( error )].
record : parser item = seq4 word (spaces1 *> lvl) (spaces1 *> word) (spaces1 *> rest)
  ([t] [l] [c] [m] '( logged $t $l $c $m. )).
$parseLines log record.     (* `ierrorAt log from to msg` for a line that fails *)
```

## 10. Alternatives rejected

- **An `IO` monad or effect rows in the meta language** (4.4): nondeterminism, hand-declared
  dependencies, no playground. Koka-style rows are a large feature for one effect.
- **Computed paths at compile time** (`readFile` primitive): trackable by the database, but it defeats
  static safety checks, the watch list and the playground's file set. Can be added later, inside the
  roots, if a need appears.
- **Object-level string functions first** (Soufflé's `substr`, `to_number`): they invent values, so the
  termination analysis would need rules for them, and they make line parsing a puzzle of rules. The
  `pattern` and `jsonl` formats cover the common cases in the loader. Deferred to S1.
- **Only facts files, with converters outside** (Datomic, LogicBlox, extractors): this is today's state,
  and it is what the issue calls inadequate. Extractors remain the right answer for source code.
- **Silent skipping of bad records** (Nemo): hides data errors; opt-in only.
- **A parser generator in the compiler:** grammars as a library on `chars` (6.3) cost no compiler code.

## 11. Batches

Each batch is one PR. It updates the reference (`reference/src/object/io.md`, a new `std/io` chapter, and
`docs/errors/`) in the same PR, as CLAUDE.md requires, and adds golden tests and `IncrementalSuite`
cases for its claim. Line counts are rough, code plus tests plus reference.

| batch | content | lines | risks |
|---|---|---|---|
| **R1** run-time sources | `source`, `asource`, `%from` in `std/reflect`/`std/io`; path resolution and roots (8.1–8.2, 8.4); `DataTable` generalising `FactsFile`; formats `facts`, `csv`/`tsv` (label or position, constants by name), `lines`, `chars`; E0802/E0803 with spans; `--input r=FILE`, `--root`, `--allow-read` | ~1 200 | the attribute's path must be resolved relative to the directive's file through expansion and module instances; CSV dialects (quotes, CRLF, BOM) |
| **R2** tools | LSP: dynamic watchers for the files a compilation read, diagnostics on data files, hover and go to definition on paths; REPL `:input`, `:reload` of sources; `FileStamp` for large files; `bench/` CSV benchmark | ~600 | client support for dynamic registration differs by editor; the stamp's racy-clean case |
| **R3** playground file system | `files` in the request, file tabs, upload, sharing of several files, `` ```file `` blocks in the reference, `examples.mjs` including facts and data examples | ~700 | bundle size (budget of `docs/design/website.md`); URL length |
| **C1** text imports | `%import … as text/lines/source`; `src`, `ierrorAt`; size cap; string primitives (`chars`, `codepoint`, `fromCodepoint`, `parseInt`, `parseFloat`, `less`, `strlen`); library confinement (8.3) | ~800 | `less` is the meta level's first comparison: reference wording, stuck terms on non-literals; spans of `ierrorAt` through the item-slice machinery |
| **C2** `std/parse` | combinators, `many` with a progress check, `csvRows`, `lines`; reference chapter with examples 9.1 B and 9.2 B; measure of meta parsing speed | ~600 | size-change acceptance of the combinators through higher-order calls (calls through values have unknown size-change graphs, `meta/termination.md`); may need the fuel variant |
| **G1** grammars and patterns | `pattern` format (JVM regex; Scala.js `RegExp` with the same group syntax, a checked subset); compile-time check of group names against labels; `std/grammar` (CFG to rules over `chars`) generalising `%regex` | ~800 | JVM and JavaScript regex dialects differ: restrict to a common subset and test both |
| **J1** JSON | `jsonl` by label, `json` into `std/json` terms; a streaming reader | ~700 | numbers (64-bit ints versus floats), deep nesting and interning cost |
| **S1** (deferred) | object-level string functions and their termination rules; computed paths; `sha256` integrity | — | only if users need them after R1–J1 |

Order: R1, then R2, R3 and C1 in any order, then C2, G1 and J1. R1 alone answers the issue's main need
(read a CSV or a log and compute).

## 12. Open decisions for the designer

1. **Which level first.** *Recommendation:* run time (R1). It serves data, the common case, and touches
   neither the meta level nor the type theory.
2. **Surface of run-time sources:** a new `%from src r` that implies `%input`, `%input r src` with an
   optional argument, or Soufflé-style parameters. *Recommendation:* `%from`, a plain meta function
   `source -> decl -> decl`. Directives cannot be overloaded by arity, `%from` composes with `%open`
   and the prefix form, and `source` lives in a new `std/io` that the prelude opens.
3. **Static paths only at compile time?** *Recommendation:* yes, literal paths in `%import … as`.
   Revisit computed paths, inside the roots, only with a concrete need (4.4).
4. **The default read root.** *Recommendation:* the main file's directory (the workspace in the LSP),
   with `--root` and `--allow-read`; libraries confined to their own directory; run-time sources only
   from the main program (8.3–8.4).
5. **Strings at the meta level:** add `chars`, `codepoint`, `parseInt`, `parseFloat`, `strlen` and a
   comparison `less`. The meta level has had no comparisons so far, by design. *Recommendation:* add
   them as primitives of `std/reflect`, next to `same`. They are total and deterministic, and the
   rationale that "comparisons are object formulas" is about syntax, not about meta functions.
6. **JSON mapping:** a typed tree (`std/json` terms), records by label (`jsonl`), or triples (Nemo).
   *Recommendation:* `jsonl` by label first (most data), the tree second; no triples.
7. **Bad records:** fail the run, skip silently, or skip with a warning. *Recommendation:* fail after up to
   20 diagnostics by default; `skipInvalid` skips with a warning and a count.
8. **Large files in the database:** text versus a stamp. *Recommendation:* a stamp for run-time files
   over 4 MiB, text otherwise and for open buffers (5.3).
9. **Integrity hashes** (Dhall's `sha256`). *Recommendation:* not now; list hashes in `--stats`.
10. **Type providers:** let directives declare relations with columns of base types (`irelation` with
    fresh columns), so a CSV header can generate a schema. *Recommendation:* defer until after C2. It
    changes the reflection API, and the examples above need only declared relations.
11. **Facts files:** keep `--facts` and `.facts` as they are. *Recommendation:* yes; `facts "x.facts"` is
    the same format as a source, so nothing is deprecated.

## 13. Sources

Run-time input:

- Soufflé, "I/O Directives": https://souffle-lang.github.io/directives (`.input`/`.output`, `IO=file`,
  `stdin`, `sqlite`, `filename`, `delimiter`, `columns`, `compress`, `headers`, `rfc4180`, `-F`, `-D`).
- Soufflé source (mirrored in souffle-haskell 3.4.0): `cbits/souffle/io/IOSystem.h` (registered
  readers: file and stdin CSV, `json`, `jsonfile`, SQLite), `io/ReadStreamJSON.h` (names `json`,
  `jsonfile`), `io/ReadStreamCSV.h` (error messages per line and column):
  https://hackage-content-origin.haskell.org/package/souffle-haskell-3.4.0/candidate/src/cbits/souffle/io/IOSystem.h
- Soufflé, "Arguments" (functors `substr`, `strlen`, `to_number`): https://souffle-lang.github.io/arguments;
  "User-Defined Functors": https://souffle-lang.github.io/functors
- Nemo, "Imports": https://knowsys.github.io/nemo-doc/reference/imports/ (formats, `format` tuples,
  `ignore_headers`, silent skipping of lines that do not match).
- Datomic, "Query Data Reference" (`:in`, relation bindings): https://docs.datomic.com/query/query-data-reference.html
- M. Aref et al., "Design and Implementation of the LogicBlox System", SIGMOD 2015.

Compile-time IO:

- template-haskell 2.24.0.0, `Language.Haskell.TH.Syntax` (`runIO`, `addDependentFile`):
  https://hackage.haskell.org/package/template-haskell/docs/Language-Haskell-TH-Syntax.html
- Lean 4: lean4#2762 "Declare extra dependencies of Lean files" (from lake#86), closed by lean4#7703
  (`needs`): https://github.com/leanprover/lake/issues/86; Mathlib/Lean `include_str`:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Util/IncludeStr.html; Batteries
  `compile_time_search_path%`; Lean reference, "Elaboration and Compilation":
  https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/
- Rust `include_str!`: https://doc.rust-lang.org/std/macro.include_str.html; Cargo build scripts
  (`rerun-if-changed`, `OUT_DIR`): https://doc.rust-lang.org/cargo/reference/build-scripts.html
- F# type providers: https://learn.microsoft.com/en-us/dotnet/fsharp/tutorials/type-providers/;
  FSharp.Data CSV provider: https://fsprojects.github.io/FSharp.Data/library/CsvProvider.html
- Idris 2 `Language.Reflection` (`readFile : LookupDir -> String -> Elab (Maybe String)`, `idrisDir`):
  https://idris2docs.sinyax.net/data/base/docs/Language.Reflection.html; D. Christiansen, E. Brady,
  "Elaborator reflection: extending Idris in Idris", ICFP 2016.
- Racket `include`: https://docs.racket-lang.org/reference/include.html; `register-external-file`:
  https://docs.racket-lang.org/raco/cm-accomplice.html
- Zig `@embedFile`: https://ziglang.org/documentation/master/#embedFile; module path restrictions
  discussed at https://ziggit.dev/t/embedfile-refuses-to-load-file-in-src/13204 and
  https://ziggit.dev/t/anonymous-import-not-playing-nicely-with-embedfile/10484
- Dhall, "Safety guarantees": https://docs.dhall-lang.org/discussions/Safety-guarantees.html

Effects in total languages and permissions:

- Agda, "Foreign Function Interface" (`Agda.Builtin.IO`, `COMPILE GHC`):
  https://agda.readthedocs.io/en/latest/language/foreign-function-interface.html; "Postulates";
  "Safe Agda" (`--safe` forbids postulates): https://agda.readthedocs.io/en/latest/language/safe-agda.html
- E. Brady, "Programming and reasoning with algebraic effects and dependent types", ICFP 2013; Idris
  Effects tutorial: https://docs.idris-lang.org/en/latest/effects/introduction.html
- Koka book (`total`, `exn`, `div`, `console`, `ndet`): https://koka-lang.github.io/koka/doc/book.html;
  D. Leijen, "Koka: Programming with row polymorphic effect types", MSFP 2014.
- Deno, "Security and permissions": https://docs.deno.com/runtime/fundamentals/security/
- S. Shieber, Y. Schabes, F. Pereira, "Principles and implementation of deductive parsing", J. Logic
  Programming 24, 1995.

Hugin `28dbcb1`: `util/SourceFiles.scala`, `platform/Platform.scala`,
`web/src/main/scala/hugin/platform/Platform.scala`, `web/src/main/scala/hugin/web/{Hugin,Session,Request}.scala`,
`compiler/Libraries.scala`, `query/{Database,CompilerQueries,EvaluationQueries}.scala`,
`runtime/{FactLoader,InputProblems}.scala`, `syntax/FactReader.scala`, `cli/{CommandLine,Main}.scala`,
`repl/Session.scala`, `lsp/{Features,HuginLanguageServer}.scala`, `editors/vscode/extension.js`,
`site/play/{worker,share}.js`, `site/examples.mjs`, `site/example-regex.hgn`,
`src/main/resources/hugin/stdlib/std/reflect.hgn`, `reference/src/{object/io,directives,reflection,modules}.md`,
`reference/src/meta/{functions,termination}.md`, `docs/INCREMENTALITY.md`,
`docs/design/incrementality-2.md`, `docs/PERFORMANCE.md`.
