# Per-item incrementality: plan (issue #4)

Today `Compile` runs the whole pipeline per file: every edit, also whitespace, recompiles everything,
including the prelude and imported files. This note records the plan for finer-grained queries. Each
step is one PR that keeps all tests green; `IncrementalSuite` (incremental = from scratch on every golden
program under edits) is the safety net for all of them.

## Obstacles (state shared across items)

* `Sym` carried typing results (`mtype`, `static`, `sigValue`, `state`, `tparams`, `typeDef*`, `used`,
  `fnModes`); since step 3 they are in the typer's `SymTable` (read as `CompilationUnit.symbols`) and
  `Sym` holds only namer output. `Scope` carried `qualifier`/`shadowed`, which the program wrote into the
  prelude's scope; since step 4 they are MetaEval inputs.
* `CompilationUnit` maps keyed by tree identity (`imports`, `scopes`) and `deferred` closures that run
  in a later phase.
* Monomorphize mutates the generic program's `RelSym`/`TypeSym` in place.
* Equality: surface and object trees keep spans in a second parameter list (`==` ignores them), meta
  trees do not; `SourceFile` compares by identity, so `Parse` never cuts off today. A per-item query
  whose result ignores spans would keep stale positions after an edit before the item.
* Fresh names (`_17`, module prefixes, hygiene) come from counters over the whole file.

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
6. **Stable keys**: `ItemKey(scope, Named | Rule | Anon(kind, structural hash, occurrence))`,
   `ScopeKey`, `SymKey`; symbol equality by key; per-item fresh-name counters.
7. **Libraries as queries**: imports, the library graph and file elaboration as queries; the prelude
   and imported files are elaborated once per process, not once per compilation (the largest win for
   the REPL and the language server).
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
