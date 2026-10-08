# Per-item incrementality: plan (issue #4)

> **Since the redesign (step B3c of docs/REDESIGN.md)** the meta level is `hugin.core`, and its
> elaboration is incremental in parts (`core/ProgramElab`, memoised by `query/ProgramQueries`): the
> prelude and the imported files form a chain, each file elaborated in a fork of the core of the files
> before it (`ElabLibrary`); the program's declarations (declarations, definitions, clauses, edges) are
> elaborated together in a fork of the chain's core (`Signatures`, cut off by the fingerprints of the
> declaration items, `DeclarationsOf`); each object item (rule, query, directive) is elaborated on its own
> in a fork of the declarations' core (`ElabItem`, keyed by its tree and occurrence, cut off by its
> fingerprint); the program is assembled from the parts (`ElabProgram`): the family instances an item
> created are recreated in the assembled core, an item that created module instances or universe levels
> is elaborated again there. So editing an object item elaborates that item, editing a declaration the
> declarations and every object item (the old per-declaration dependencies, `DeclSig`, `ScopeName`, are
> not ported: the meta level's declarations are dependently typed and refer to each other by value), and
> moving items elaborates nothing. The sections below describe the plan as it was carried out for the
> meta level before the redesign; the names in them (`Sym`, `SymTable`, `ScopeOf`, MetaEval) are gone.

Today `Compile` runs the whole pipeline per file: every edit, also whitespace, recompiles the program;
since step 7 the prelude and imported files are named and elaborated once per database revision and
shared by all compilations, and since step 8 the items of the program are elaborated one by one, so an
edit elaborates again only the items it affects (the object-level pipeline still runs per edit), and since
step 9 the items are parsed from their own text slices, so an edit does not elaborate the items it only
moves; step 10 made the clients (diagnostics, the language server, the REPL) and the database's memory
follow (see *Status* at the end). This note records the plan for finer-grained queries. Each
step is one PR that keeps all tests green; `IncrementalSuite` (incremental = from scratch on every golden
program under edits) is the safety net for all of them.

> **Directives (C2)** are object items like rules: a local directive (`%input r.`, one returning a
> `decl`) and an additive one (returning items) are elaborated on their own, so editing one elaborates
> that item only. A module-wide directive (`module -> module`) makes the file's rules and queries depend
> on its expansion, which runs when the program is assembled (`ElabProgram`); the items are still
> elaborated one by one for their diagnostics and index. A prefix directive is parsed from a slice that
> includes the declaration it is attached to (docs/NOTES.md, "Directives").

## Obstacles (state shared across items)

* `Sym` carried typing results (`mtype`, `static`, `sigValue`, `state`, `tparams`, `typeDef*`, `used`,
  `fnModes`); since step 3 they are in the typer's `SymTable` (read as `CompilationUnit.symbols`) and
  `Sym` holds only namer output. `Scope` carried `qualifier`/`shadowed`, which the program wrote into the
  prelude's scope; since step 4 they are MetaEval inputs.
* `CompilationUnit` maps keyed by tree identity (`imports`, `scopes`) and `deferred` closures that run
  in a later phase; since steps 4–6 imports are resolved at use, module-body scopes are keyed by
  `ScopeKey` and requirement checks are data.
* Monomorphize mutated the generic program's `RelSym`/`TypeSym` in place (they are created by MetaEval
  per compilation, so this did not touch shared library results); it now copies the monomorphic
  declarations, so the generic program stays as MetaEval produced it. The object-level phases no
  longer write into the symbols either: directives are `ProgramFacts` on the unit (keyed by symbol,
  replaced when a later phase adds a relation), runtime tags are the core IR's.
* Libraries: since step 7 a library's `Scope`, `SymTable` and `SymKeys` are frozen once elaborated and
  read through the program's layered table; MetaEval still evaluates every library once per compilation
  (its object names depend on the program: the prelude's `prelude.n` when the program shadows `n`, the
  numbered prefixes `geo2`). A `%mode` written in a file for a prelude formula function is seen by that
  file only (copy-on-write); the prelude has no formula functions.
* Equality: surface and object trees keep spans in a second parameter list (`==` ignores them), meta
  trees do not; `SourceFile` compares by identity, so `Parse` never cuts off. A per-item query whose
  result ignores spans would keep stale positions after an edit before the item; since step 9 the spans
  of a program's items are relative to their slice and resolve through its placement in the current text.
* Fresh names (`_17`, module prefixes, hygiene) come from counters over the whole file; since step 6 the
  typer's counters (anonymous Π-parameter names, local scope keys) are per item, MetaEval's module
  prefixes and hygiene counters are still global (MetaEval stays whole-program).
* Elaboration order: the typer elaborated meta definitions in item order and object declarations and type
  definitions on demand, from whichever item used them first; `ElabState` gave E0105 for a use of a later
  definition. Since step 8 the declarations are elaborated before the other items and an item does not
  see the meta definitions of later items (a static check by item order). Only the position of E0104 in
  a cycle of type definitions entered first from a rule, query, directive or edge could differ (no
  golden test has one).

## Steps

0. **Safety net** (this PR): `IncrementalSuite`, golden tests for every diagnostic code, a test that the
   `hugin explain` catalog equals the emitted codes, phase timings in `--stats`.
1. **Dead state and settings split.** Delete `Sym.order`, `Scope.processed`; `Sym.kind`/`decl` immutable;
   split the options into what the compiler produces (`Settings`: prelude, lint, and print-after,
   stop-after and explain-termination, whose output is part of a compilation) and how diagnostics are
   shown (`Display`: colour, warnings), so only the former key `Compile`.
2. **Database: accumulated diagnostics and cycle recovery.** Diagnostics as accumulated outputs of a
   query (replaced on recomputation even when the value cuts off); `Query.onCycle` fallbacks for object
   declarations and type definitions (E0104).
3. **Typer state out of `Sym`** into a typer-owned symbol table (in three parts: meta types; declaration
   signatures and type definitions; immutable namer output, `used` from index references, `fnModes`
   from a pre-pass).
4. **Naming state into MetaEval**: qualifiers and prelude shadowing become MetaEval inputs.
5. **No identity-keyed unit maps**: resolve imports at use, scopes by key, requirement checks as data.
6. **Stable keys** (done, `meta/Keys.scala`): `ItemKey(scope, Named | Rule | Anon(kind, structural hash,
   occurrence))`, `ScopeKey` (`File`, `Module`, `Params`, `Local`), `SymKey(scope, name)`; symbol equality
   by key, with a check that no two symbols of a compilation share one (`SymKeys`); per-item fresh-name
   and local-scope counters in the typer. Items are keyed by name or by a span-insensitive hash of their
   tree, never by index, so inserting or editing an item keeps the keys of the others (`KeysSuite`).
7. **Libraries as queries** (done, `compiler/Libraries.scala`, `query/CompilerQueries.scala`): `Imports`
   (the resolved imports of a file), `LibraryGraph` (the program's walk of its imports: files in
   dependency order, missing files, the imports that close a cycle, parse diagnostics and E0108, cut off
   when the imports stay the same), `NameLibrary` (a file's frozen scope) and `ElabLibrary` (its body,
   module value, frozen typing results, symbol keys, part of the semantic index and diagnostics, also
   pushed to the `LibraryDiagnostics` accumulator). A library's elaboration is keyed by its path, the
   prelude flag and the imports cut by cycles (empty for an acyclic graph, so all programs share it); it
   depends only on the prelude and on the files it imports, so the keys never form a query cycle and an
   edit invalidates exactly the dependants. Which import of a cycle is reported depends on where the
   walk enters it, so the graph and its diagnostics belong to the program. The program's typer layers
   its `SymTable` and `SymKeys` over those of its libraries (reads fall through, writes stay local) and
   includes their semantic index; the namer and typer phases report the libraries' diagnostics in the
   same order as before. The REPL and the language server keep one database, so the prelude is
   elaborated once per session (`LibraryQueriesSuite`, `IncrementalSuite` with library edits).
8. **Per-item elaboration** (done, partly: declarations are elaborated together; `compiler/ProgramElab.scala`,
   `query/CompilerQueries.scala`). The program's top level is elaborated in parts:
   * `ScopeOf` names it (a frozen scope); its value is equal, and cut off, as long as the items the namer
     and the elaboration of declarations read are equal with their positions (declarations and
     definitions, clauses of formula functions, `%mode`s of formula functions; see `ItemFingerprint`) and
     the prelude is the same, so a cut-off keeps symbols whose spans are still right. `ScopeNames` (the
     names, kinds and keys of the top level) is what name resolution in an item depends on.
   * `Signatures` elaborates all declarations and definitions together, in item order, as the typer did
     (object declarations and type definitions on demand, meta definitions in order with the dynamic
     `ElabState` check for E0104/E0105 among them). `DeclSig` projects it per declaration item (the
     fingerprints of the item and of the clauses of a formula function, and the typing results of all its
     symbols, compared with positions by `Positional.same`); it stands for the planned `DeclSig`,
     `TypeDefSig`, `MetaDefType` and `MetaDefResult`, which are one projection here because any edit of an
     item changes its fingerprint anyway. A `%mode` of a prelude formula function is a part of its own.
   * `ElabItem` elaborates one other item (rule, query, directive, subtyping edge) with its own typer,
     whose table is layered over the signatures' table. It depends on the item with its position
     (`ItemOf`), on `ScopeNames`, on the libraries (`ProgramLibrariesOf`), on the declarations after it
     (`LaterDecls`) and on the `DeclSig` of every declaration it read: the table's `View` and the scope's
     `observing` hook record every symbol an item reads from the signatures or finds in the top-level
     scope (step 10 replaces `ScopeNames` and `LaterDecls` by finer dependencies). The scope and the signatures themselves are read untracked (`Database.untracked`), since these
     dependencies cover what the item uses of them. The static forward-reference check replaces
     `ElabState` for items: the view hides the meta definitions and formula functions of later items (they
     read as not elaborated, as they were when the body was elaborated in item order), which gives E0105.
   * `ElabFile` assembles the parts in item order (the body, a merged table, keys, semantic index, scopes,
     diagnostics); the typer phase reads it. Diagnostics of the parts are also pushed to the
     `ProgramDiagnostics` accumulator. Compilations without a database run the same parts in sequence
     (`ProgramElab.direct`), so both agree. The object-level pipeline and MetaEval stay whole-program.

   Editing a rule elaborates that rule again, and the items whose position changed; editing a declaration
   elaborates the items that use it; adding or removing a declaration (a change of the names) elaborates
   every item (`ItemQueriesSuite`; since step 10 only the items using its name). Positions (as of step 8; step 9 makes them item-relative): an item's
   results keep spans into the source file it was parsed from, and they are reused only while the item's fingerprint (tree, offsets, first
   line, text of its lines) is unchanged, so every reused span has the same offset, line, column and line
   text in the current file; diagnostics are moved to the current source file (`Context.sources`), and the
   semantic index compares symbols by key. The price is that an edit that changes the length or the lines
   of an item elaborates every later item again (also their declarations' dependants when declarations
   move); step 9 removes it. Remaining: declarations and definitions are elaborated together (a change of
   one elaborates all of them again, though only the items using a changed one follow); a change of the
   names of the top level elaborates every item (step 10 removes it); `ElabFile`, the object pipeline and MetaEval run after
   every edit.
9. **Item slices** (done for the program's files; `syntax/Slices.scala`, `util/Source.scala`,
   `query/CompilerQueries.scala`). Items are parsed from their own text with item-relative spans:
   * `ItemSlices(file)` parses the file as a whole (`Parse`, as before): that parse decides where the
     top-level items are, with all its error recovery (a nested module body `{ ... }` is part of its item,
     an item missing its `.` ends where the parser recovered), and it reports the parse diagnostics, so
     they are unchanged. Every item's text (from its first to its last character) is a *slice*.
   * `ParseItem(slice)` parses one slice on its own, keyed by the file's path, the text, the file's
     `%infix` operators (which the parser collects from the whole file) and the number of identical items
     before it (a slice has one placement, so identical items are different slices). It reads nothing, so
     identical text yields the very same tree after any edit elsewhere.
   * The boundary (`ItemOffsets`): a slice is a `SourceFile` placed at an offset of its file
     (`SourceFile.place`), and `ItemSlices` places the slices of the current text. A `Span` keeps its
     origin (file or slice) and offsets in it (`from`, `until`); `source`, `start` and `end` resolve
     through the placement to the current file. So every consumer (diagnostics and their rendering, the
     semantic index and the IDE queries, `--print-after`, the REPL's blanking of answered queries, the
     object phases) sees file positions without a mapping of its own, byte-identical to a parse of the
     whole file; equality and hashing of spans use the origin and its offsets, so they are stable when a
     slice moves. Instead of mapping every output at the boundary, positions are resolved lazily when read:
     the placement is the only state that changes when an item moves, and it is set before any query of
     the revision reads the items (they all depend on `ItemSlices` through `ParseProgram`).
   * A slice is used only if it parses without diagnostics into one item that is *congruent* to the item
     of the whole file: the same tree with the same positions once placed (`Slices.congruent`, which also
     compares the spans trees keep beside their fields). Otherwise (parse errors in the item, or a context
     dependence the slice parse does not see) the item of the whole file is used, with step 8's absolute
     fingerprint. On the golden programs without parse errors every item is a slice (`ItemQueriesSuite`).
   * Item fingerprints are item-relative (`ItemFingerprint`: the tree, the slice by identity and the
     offsets in it), and `Positional.same` compares spans in slices by slice and offsets, so `ItemOf`,
     `ScopeOf` and `DeclSig` cut off when an edit only moves items. The few places in elaboration that
     made a span from a span's offsets keep the origin (`Span.startPoint`, `endPoint`).

   Inserting blank lines or comments between items, or moving items to other lines and columns,
   elaborates nothing; lengthening one rule elaborates that rule only (`ItemQueriesSuite`). Remaining:
   libraries (the prelude, imported files) are still parsed and elaborated as whole files, with spans into
   the file (an edit of a library elaborates it again anyway); slices were never evicted from the database
   (step 10 evicts them); a change of the `%infix` operators parses every item again; the whole file is still parsed
   after every edit (cheap; it decides the item boundaries and reports parse errors).
10. **Clients** (done; `query/FileDiagnostics.scala`, `query/Database.scala`, `lsp/`, `repl/Session.scala`).
    * *Diagnostics per file.* `FileDiagnostics.of(key)` gives a compilation's diagnostics by file (the
      program's files and every library, in path order); concatenated they are `Compiled.diagnostics`
      (`IncrementalSuite` and `FileDiagnosticsSuite` check this for every golden program, also under
      edits). The diagnostics of the elaboration are read from the accumulators of the queries that
      computed them: a library's from `LibraryDiagnostics` pushed by its `NameLibrary` and `ElabLibrary`
      (shared by every program importing it), the program's from `ProgramDiagnostics` pushed by
      `ScopeOf`, `Signatures` and each `ElabItem` (`Database.pushed` reads a query's own pushes). The
      compilation contributes what its own phases report (parse and import errors, the typer's
      unused-definition warnings, the object-level phases) and the order in which it reported the parts
      (`Context.reported`, `Context.reportPart`); the output is assembled in that order with the
      compiler's deduplication, placement in the current text and sorting.
    * *The language server publishes per file*: each open document from its own compilation, and every
      file it imports that is not open on that file's URI (the library's group of `FileDiagnostics`). An
      open document is published after every change, as before (the transcripts are unchanged); a file
      that is not open is published only when its diagnostics changed, and cleared when they disappear (it
      is no longer imported, or it was fixed on disk: `workspace/didChangeWatchedFiles`). Fixing a file on
      disk exposed a bug in the database, also fixed: an input removed and read again from its default (a
      file read from disk) was dated revision 0, so results computed from its old value were reused.
    * *Names and order as dependencies.* An item no longer depends on all names of the top level
      (`ScopeNames`) and on all declarations after it (`LaterDecls`, removed): the scope's observer records
      every name the item looks up, found or not (`ScopeName(program, name)`: the kind and key of its
      symbol, or none), whether it listed all names (for the suggestion of a similar name; it then depends
      on `ScopeNames`), and the meta definitions whose order relative to it decided whether they are
      hidden (`DeclAfter(item, decl)`). So adding or removing a declaration elaborates only the items that
      use its name (`ItemQueriesSuite`); in a REPL session, a new input elaborates its own items only.
    * *REPL probes as an extra item.* A query typed in the REPL was already one more item of the session's
      program; the probes of `:type`, `:kind` and completion were a separate program (`<probe>`) of the
      session's parts and the probe, with keys of its own, so every item of the session was elaborated
      again for them. Now the probe is one more part of the session's program itself, removed afterwards,
      and the position queries ask about the probe's file (`Ide`'s `in`). A query or an object probe
      elaborates one item, a meta probe (`it'repl = expr.`, a definition) only the declarations
      (`SessionSuite` counts the executions). Restoring the session after a meta probe makes the next
      input elaborate the declarations again (they are elaborated together).
    * *Eviction.* `Database.collect` drops the memos that are not reachable, along recorded dependencies,
      from the queries demanded from outside any query (roots) in the last `retainEpochs` epochs
      (revisions in which queries were demanded; default 2) or from the memos verified in them: the slices
      (`ParseItem`) and items (`ItemOf`, `ElabItem`, ...) of texts and keys that no longer exist, and
      programs no longer asked about. It runs when an epoch starts and the number of memos exceeds both
      `collectAbove` (default 1024) and twice the number the last collection kept, so its cost is
      amortised. Dropping is always safe: a dropped result is computed again, kept memos keep their
      dependencies, and an item's fingerprint compares its slice by identity, so a slice parsed again is a
      change, never a stale position. Under 500 random edits of a golden program the memos stay within 4
      times those of a compilation from scratch, with results equal to it (`ItemQueriesSuite`,
      `DatabaseSuite`).

The object-level phases (stratification, demand, termination, lowering) stay whole-program: they are
global by nature and cheap compared with elaboration (`--stats` shows the split).

## Status (after step 10)

Incremental now:
* Parsing: the whole file is parsed after every edit (it decides the item boundaries and reports parse
  errors); the items are parsed from their own slices, memoised by text.
* Libraries (the prelude, imported files): named and elaborated once per revision of the files they
  depend on, shared by all programs, by the REPL session and by the language server's documents.
* The program's top level: named after every edit (cut off unless declarations change); declarations and
  definitions are elaborated together when one of them changes; every other item is elaborated on its
  own, again only when its text, a name it looks up, a declaration it reads or the order of a meta
  definition it asked about changes. Moving items (blank lines, comments, other items growing)
  elaborates nothing.
* Clients: diagnostics by file from the accumulators; the language server publishes per file; REPL
  queries and probes are extra items over the session's elaborated items; unused memos are evicted.

Still coarse:
* `ElabFile` (assembling the items), MetaEval, monomorphization and the object-level phases (directives,
  object typing, moding, records, demand, stratification, completeness, termination, lowering) run on
  the whole program after every edit, and evaluation after every REPL query: they are global by nature
  (the demand transformation depends on the queries) and cheap next to elaboration (`--stats`).
* Declarations and definitions are elaborated together (`Signatures`): editing one elaborates all of
  them again, though only the items using a changed one follow. A meta probe in the REPL is a
  definition, so it and the next input elaborate the declarations again.
* Libraries are elaborated as whole files (an edit of a library elaborates it, and the files importing
  it, again); a change of the `%infix` operators of a file parses all its items again.
* The slices' placement (`SourceFile.place`) is mutable state set by `ItemSlices`; it relies on the
  database being single-threaded (the language server answers on lsp4j's single message thread).
* The language server republishes every open document's diagnostics after any change.
