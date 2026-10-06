# Per-item incrementality: plan (issue #4)

Today `Compile` runs the whole pipeline per file: every edit, also whitespace, recompiles the program;
since step 7 the prelude and imported files are named and elaborated once per database revision and
shared by all compilations. This note records the plan for finer-grained queries. Each
step is one PR that keeps all tests green; `IncrementalSuite` (incremental = from scratch on every golden
program under edits) is the safety net for all of them.

## Obstacles (state shared across items)

* `Sym` carried typing results (`mtype`, `static`, `sigValue`, `state`, `tparams`, `typeDef*`, `used`,
  `fnModes`); since step 3 they are in the typer's `SymTable` (read as `CompilationUnit.symbols`) and
  `Sym` holds only namer output. `Scope` carried `qualifier`/`shadowed`, which the program wrote into the
  prelude's scope; since step 4 they are MetaEval inputs.
* `CompilationUnit` maps keyed by tree identity (`imports`, `scopes`) and `deferred` closures that run
  in a later phase; since steps 4–6 imports are resolved at use, module-body scopes are keyed by
  `ScopeKey` and requirement checks are data.
* Monomorphize mutates the generic program's `RelSym`/`TypeSym` in place (they are created by MetaEval
  per compilation, so this does not touch shared library results).
* Libraries: since step 7 a library's `Scope`, `SymTable` and `SymKeys` are frozen once elaborated and
  read through the program's layered table; MetaEval still evaluates every library once per compilation
  (its object names depend on the program: the prelude's `prelude.n` when the program shadows `n`, the
  numbered prefixes `geo2`). A `%mode` written in a file for a prelude formula function is seen by that
  file only (copy-on-write); the prelude has no formula functions.
* Equality: surface and object trees keep spans in a second parameter list (`==` ignores them), meta
  trees do not; `SourceFile` compares by identity, so `Parse` never cuts off today. A per-item query
  whose result ignores spans would keep stale positions after an edit before the item.
* Fresh names (`_17`, module prefixes, hygiene) come from counters over the whole file; since step 6 the
  typer's counters (anonymous Π-parameter names, local scope keys) are per item, MetaEval's module
  prefixes and hygiene counters are still global (MetaEval stays whole-program).

## Steps

0. **Safety net** (this PR): `IncrementalSuite`, golden tests for every diagnostic code, a test that the
   `hugin explain` catalog equals the emitted codes, phase timings in `--stats`.
1. **Dead state and settings split.** Delete `Sym.order`, `Scope.processed`; `Sym.kind`/`decl` immutable;
   split `Settings` into semantic `CompileOptions` (prelude, lint) and rendering/reporting options
   (colour, warnings, print-after, stop-after, explain-termination), so only the former key `Compile`.
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
8. **Per-item elaboration**: `ScopeOf`, `DeclSig`, `TypeDefSig`, `MetaDefType`/`MetaDefResult`,
   `ElabItem` (with its part of the semantic index), `ElabFile`; a static forward-reference check
   replaces `Sym.state`; the object pipeline stays one query over the elaborated file.
9. **Item slices**: items parsed from their own text slices with item-relative spans, mapped to file
   positions at the boundary (`ItemOffsets`, generalizing the REPL's former chunk mapping), so that
   whitespace and comment edits cut off.
10. **Clients**: diagnostics per file from accumulators, the language server publishing per file, REPL
    probes as an extra item, eviction of unused memos.

The object-level phases (stratification, demand, termination, lowering) stay whole-program: they are
global by nature and cheap compared with elaboration (`--stats` shows the split).
