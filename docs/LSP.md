# The language server and the meta level

`hugin lsp` serves the Language Server Protocol over stdio (`src/main/scala/hugin/lsp`), answering
through the query database (`hugin.query`): `Ide` for the position queries that `hugin query` and the
REPL share, `MetaIde` and `Expansion` for what only language servers show. This page records what the
server does for meta-level code (issue #54): the audit it started from, the features, the protocol, and
the test of each feature.

## Audit (before #54)

The server was built for the object level and covered the meta level only where the semantic index
happened to know it:

| feature | object level | meta level before #54 |
|---|---|---|
| diagnostics, quick fixes | yes | yes (the compiler's diagnostics and suggested edits) |
| hover | signatures, object variables' types, staging notes, family instances | signatures of globals and meta parameters; nothing on expressions (no types, no stages), on pattern variables, lambda parameters, `where` bindings, holes; `%d` showed the directive's declared footprint only |
| definition, references | yes | globals and meta parameters only: not pattern variables, constructors in patterns, lambda parameters, `where` bindings, clause names, variables used in quotes |
| semantic tokens | relations, types, constructors, object variables | every meta global was a `namespace`; no distinction of meta and object names, of meta functions, families and constructors; directives, quote delimiters, `$` and `⇑` were left to the grammar |
| inlay hints | none | none (inserted quotes, splices, implicit arguments only visible with `--print-after elaborate`) |
| staged output | none | none: no way to see what a directive or functor application produced |
| interactive development | none | none: no holes; coverage errors named the first missing case only |
| completion | scope, labels, members, directives | scope-based only: no expected type, no quote awareness |

Broken items (syntax errors) are dropped by the resilient parser (#53), so features inside them still do
not work (see "Deferred" in `docs/NOTES.md`, "LSP for the meta level (#54)").

## Features

- **Hover** adds to the signature and the staging notes: the elaborated type of the innermost expression
  under the cursor (types are shown with the solutions of their unknowns) and its *stage* (`meta`,
  `object`, or `meta, object code ⇑A`); the elaborated term when it shows what was not written
  (implicit arguments `{int}`, quotes `⟨…⟩`, splices `$…`); for a typed hole its goal and the variables
  in scope; inside a directive application `%d …` its type and footprint; on a shared type or
  constructor both stages and the derived `T.lift`/`T.reify`.
- **Navigation**: pattern variables, lambda parameters and `where` bindings are declared and their uses
  recorded (also in reflection quotes); constructors in patterns and clause names are references.
- **Semantic tokens**: legend types `namespace type struct function enumMember macro parameter variable`
  (as before) plus `decorator` (directives), `keyword` (`'{`, `}` of quotes), `operator` (`$`, `$..`,
  `⇑`), `method` (meta functions), `class` (meta families and types), `label` (typed holes); modifiers
  `declaration`, `meta`, `object`, `defaultLibrary` (prelude names).
- **Inlay hints** (`inlayHintProvider`): the quotes, splices, liftings and lifts stage inference inserted
  (`staging`), inferred implicit arguments (`implicits`), universe levels (`levels`). Configured by the
  initialization option `{ "inlayHints": { "staging": true, "implicits": true, "levels": false } }` and
  by `workspace/didChangeConfiguration` with `{ "hugin": { "inlayHints": { … } } }`; the server asks the
  client to refresh its hints if it supports that.
- **Staged output**: the command `hugin.expansion` (`workspace/executeCommand`, arguments
  `[uri, line, character]` or `[{ "uri", "position" }]`) returns the object rules and queries the
  directive or functor application at the position produced (or the staged instances of the item
  there), each with the rest of its expansion chain, as Hugin text (null if there is nothing). Code
  lenses `Show expansion (n items)` on every application that produced items run the client command
  `hugin.showExpansion` with `[uri, line, character]`.
- **Typed holes** (`?`, `?name`, E0924): the diagnostic's `data` is
  `{ "goal", "name"?, "stage", "context": [{ "name", "type" }] }`; hover shows the goal.
- **Code actions**: `Split on X` (`refactor.rewrite`) on a pattern variable of an inductive type
  replaces its clause by one clause per constructor whose indices unify; `Add the missing clause(s)`
  (preferred quick fix of E0911) inserts every case the coverage checker found, with holes; `Add a
  clause for f` on a meta function declared without clauses.
- **Completion**: after `%` the directives; inside a reflection quote only object syntax (after `$`, only
  meta values); where the elaborator checked the name being typed against a known type, the candidates
  whose result type has the same head come first (`preselect`, `sortText`) and the variables in scope
  there are offered.

## Tests

One transcript per feature in `tests/lsp` (replayed by `TranscriptSuite`), precise assertions in
`MetaLanguageServerSuite`:

| feature | transcript |
|---|---|
| hover | `meta_hover.in` (and `hover_staging.in`) |
| navigation | `meta_navigation.in` |
| semantic tokens | `meta_tokens.in` |
| inlay hints | `meta_inlay_hints.in` |
| staged output | `meta_expansion.in` |
| holes, code actions | `meta_holes.in` |
| completion | `meta_completion.in` |
