# Editor features on the web: the playground and the reference

Design note for [issue #147](https://github.com/k0uks1/hugin/issues/147) (the language server's editor
features in the playground, computed by the compiler in the playground's Web Worker) and
[issue #132](https://github.com/k0uks1/hugin/issues/132) (hover and go to definition in the reference's
code samples, computed at build time). Status: round 1, for the designer's approval. Nothing is
implemented. The measurements this note cites were made against `a1a4274`
(`origin/ccr-48027e29-daam41`) in a scratch copy and are not committed.

The binding rules are those of #58 and `docs/design/website.md`: prior art first; the site stays fast
and slim, with static pages, no heavy framework and no tracking; the editor is CodeMirror 6. Both issues
are tooling only: no batch changes the language, the reference text or the diagnostics.

Contents: 1 recommendations, 2 Hugin today, 3 prior art, 4 the shared core, 5 the worker protocol,
6 the playground, 7 the reference, 8 bundle size and latency, 9 accessibility, 10 alternatives
rejected, 11 batches, 12 open questions, 13 sources.

## 1. Recommendations

1. **One feature layer, `hugin.ide`, three consumers.** The protocol-independent half of `lsp/Features`
   and `lsp/MetaFeatures` (what hover shows, which completions fit, which fixes apply, how the outline
   nests) moves into the shared package `hugin.ide`, next to `Tokens` and `Highlighting` from #145. It
   speaks in character offsets (UTF-16, which is what JVM strings, Scala.js strings and CodeMirror
   positions all use) and plain case classes. The language server keeps only the encoding: URIs,
   line/character positions and lsp4j types. The browser build and `hugin highlight` call the same
   functions (4).
2. **One data product for hover-like features: the annotation table.** A new
   `hugin.ide.Annotations.of(file)` computes, for a whole file in one pass, every name's hover text, its
   definition (in the file, or a library declaration) and its occurrence group. The same table serves
   both issues: `hugin highlight --info` writes it at build time for the reference (#132), and the
   worker returns it with every highlighting for the playground (#147). Hover, go to definition,
   references and occurrence highlighting are then answered **on the main thread from the table**, with
   no worker round trip and no recompilation per hover (4.3, 6.1).
3. **Requests only for what depends on the cursor:** completion, code actions at the cursor and the
   meta expansion are worker requests, answered from a database that **persists in the worker** between
   requests, so a request after a highlighting reuses its compilation (5).
4. **CodeMirror's own extensions, no LSP client.** `hoverTooltip` (already in `@codemirror/view`) and
   `@codemirror/autocomplete` cost +9.1 KB gzip on the playground's 111 KB. `@codemirror/lsp-client`
   would cost +31.3 KB gzip and need an LSP JSON-RPC layer in the worker, which lsp4j cannot provide
   under Scala.js (8.1, 10). The playground borrows its key bindings (F12, Shift-F12, Ctrl-Space).
5. **The reference: Verso's model, slimmer.** Static spans carry a small index into a per-page,
   deduplicated table of hover texts, embedded in the page as JSON, as Verso does with
   `data-verso-hover` and `-verso-docs.json`. Definitions are ordinary links, so they work without
   JavaScript. A ~3 KB script (no tippy.js, popper.js or marked) shows one shared popup. Not CSS-only:
   popups would be clipped by the horizontally scrolling `<pre>`, every name would need its own tab stop,
   and on touch screens a popup could not be closed (7.3). Measured: the largest page gains 4.7 KB gzip,
   the median page 0.8 KB. Budget: **at most 8 KB gzip of added data per page** (7.4).
6. **Accessible by keyboard and touch from the start.** In the reference, a code block is one tab stop,
   arrow keys move between its names and show their popup, and a tap shows the popup instead of
   following the link. In the playground, an info bar under the editor shows what is at the cursor, so
   touch and keyboard users get the hover text without a mouse; Ctrl-K Ctrl-I opens the tooltip (9).
7. **Seven batches, one PR each:** the shared layer first (I1, I2), then the reference (R1) and the
   playground (P1 to P4) in parallel (11).

## 2. Hugin today

### 2.1 What the language server has

`src/main/scala/hugin/lsp/` on `a1a4274`:

| file | lines | content |
|---|---|---|
| `Features.scala` | 305 | documents, diagnostics, hover, definition, references, completion, outline, semantic tokens, expansion, inlay hints, code actions, all in lsp4j types |
| `MetaFeatures.scala` | 212 | meta-level hover, inlay hints and their settings, typed-hole goals as JSON, interactive code actions (split, add the missing clauses, add a clause, refine a hole), expansion lenses, type-directed completion |
| `HuginLanguageServer.scala` | 216 | the lsp4j server: capabilities, request dispatch |
| `Worker.scala` | 111 | the request thread and cancellation (#126) |
| `Tokens.scala` | 30 | the semantic tokens' delta encoding over `hugin.ide.Tokens` (#145) |
| `Positions.scala`, `Uris.scala` | 34, 30 | offsets to LSP positions, paths to URIs |

Below `lsp/` lie the compiler's position queries in `hugin.query`: `Ide` (hover information, symbol at,
definition, references, completions, symbols; used by the LSP, the REPL and the hidden `hugin ide`
command), `MetaIde` (goals, hints, splits, missing clauses, expected types) and `Expansion`. They are
already protocol-independent and compile for Scala.js. What is not shared is the layer between them
and the protocol, and it holds real decisions:

- **hover** merges `Ide.hoverInfo` and `MetaIde.hover`, drops duplicates and answers nothing between
  tokens (`MetaFeatures.hover`'s `onToken`);
- **completion** finds the prefix being typed, keeps only object syntax inside a reflection quote
  `'( … )` (meta values after `$`), adds the meta variables in scope where the elaborator knew the
  expected type, and ranks the candidates whose result type fits first;
- **code actions** turn diagnostics' suggestions into fixes (only the first machine-applicable one is
  preferred), drop fixes with edits in the bundled library, and add the meta-level actions, including
  the text of a split clause;
- **outline** nests declarations by their enclosing module bodies;
- **inlay hints** filter by the settings `staging`, `implicits` and `levels`.

All of it is written against lsp4j types (`Position`, `CompletionItem`, `CodeAction`, `WorkspaceEdit`,
gson's `JsonObject`), so none of it compiles for the browser.

### 2.2 The playground and the reference

- **Playground** (`site/play/`, `web/src/main/scala/hugin/web/`): `main.js` starts `worker.js`, which loads
  `hugin.js` (the Scala.js bundle) and answers `{ id, op: "run" | "check" | "highlight", source,
  printAfter }`. Requests are tracked by id. A request that exceeds the 10 s budget terminates and
  restarts the worker. A `highlight` request goes out after 400 ms without typing, not while a run is
  busy, and an answer whose source is no longer the editor's is dropped (#145). Every call compiles
  in a **new** `Database` (`Playground.compile`, `Playground.highlight`); only the parsed standard library
  is shared (`StdlibCache`). Diagnostics use the JSON format with 1-based lines and columns. Their
  suggestions are buttons, and they are actions of `@codemirror/lint`.
- **Reference** (`reference/highlight.py`, an mdBook preprocessor): all `hugin` blocks of the book go
  in one JSON array to `hugin highlight` (`cli/Highlight.scala`), which compiles each in one shared
  database and returns runs `[text, [class, …]]` from `hugin.ide.Highlighting`. The preprocessor writes
  `<pre><code class="hugin hljs nohighlight">` with `hg-*` spans. The landing page (`site/build.mjs`)
  uses the same command and loads no JavaScript besides the theme switch.
- **Reference size:** 33 pages hold 183 `hugin` blocks (plus the error index's). The largest page,
  `reflection.md`, has 17 blocks and about 690 identifier occurrences, and the median page has about 140.

## 3. Prior art

Clones are shallow, made on 2026-10-10 (13).

### 3.1 Lean 4: Verso and SubVerso (build-time hovers)

The closest model for #132. **SubVerso** stores highlighted code with the elaborator's information
for each token. Its `Token.Kind` (`SubVerso/Highlighting/Highlighted.lean`) has `const (name, signature,
docs, isDef)`, `var (fvarId, type)`, `keyword (name, occurrence, docs)`, `str`, and more. **Verso** renders
this into static HTML (`Verso/Code/Highlighted.lean`):

- every token is a `<span class="… token">` with `data-binding` (an occurrence group) and
  `data-verso-hover="N"`;
- the hover contents are HTML fragments, **deduplicated** while the site is generated
  (`Hover.Dedup`: content to id) and written once **for the whole site** to `-verso-docs.json`, which the
  page fetches (`fetchDocsJson`);
- messages (errors, warnings) are inline `hover-info` spans;
- definitions link to the documentation of the constant;
- a ~200-line script highlights all occurrences of a binding on mouse-over and creates tooltips with
  **tippy.js and popper.js** (25.7 KB and 20.1 KB minified, vendored). It renders docstrings with
  **marked**. The tooltips are interactive, appended to `<body>`, and have a 100 ms delay.

The tokens are plain spans without `tabindex`, so the hovers are **not reachable by keyboard**.
Verso's CSS enables hover backgrounds under `@media (hover: hover)` only. Touch gets tippy's default:
a tap shows the tooltip.

### 3.2 lean4web (live.lean-lang.org)

"This is a web application running Lean 4 **server-side**" (README). `server/index.mjs` proxies LSP
JSON-RPC over a WebSocket to `lake serve` in a bubblewrap sandbox. The client is React with Monaco
through `lean4monaco`, which reuses the VS Code extension's code, infoview included. It has every
editor feature, at the price of a server and a heavy client. The protocol is unchanged LSP.

### 3.3 Rust Playground

Server-side compilation in Docker. The editor is Ace or Monaco. The only editor intelligence is a
completion provider for crate names after `use` or `extern crate`
(`ui/frontend/editor/MonacoEditorCore.tsx`). It has no hover and no go to definition: rust-analyzer does
not run there.

### 3.4 Scastie and Metals

Scastie's client is Scala.js on CodeMirror 6. Hover, completion, signature help and diagnostics come
from a **server-side Metals** (the `metals-runner` service). The client posts the whole document and an
offset to `/metals/<endpoint>` for every request (`MetalsClient.scala`), and `MetalsHover.scala` wraps
CodeMirror's `hoverTooltip` around it and renders Markdown with marked. It is a useful precedent for
CodeMirror's tooltip API with stateless, offset-based requests. No experiment that runs Metals or the
Scala presentation compiler **in the browser** was found.

### 3.5 Koka, Roc, Gleam

- **Koka** (`koka-lang/koka`, `web/playground/`): the compiler **and its language server** are
  compiled to Wasm and run in Web Workers. They give hover, completion, diagnostics, inlay hints and go
  to definition in Monaco (React). The LSP worker reads stdin through `SharedArrayBuffer` and
  `Atomics.wait`, which needs cross-origin isolation (`coi-serviceworker`). The CI builds and tests it
  but does not deploy it (`PLAYGROUND.md`). This is the only in-browser compiler-backed editor found, and
  it confirms that the same server code can answer in a worker. It also shows the cost of speaking LSP
  in the browser: a service worker for the headers, and a full LSP client.
- **Roc**: the web REPL compiles the compiler to Wasm (`crates/repl_wasm`). Later commits add
  `QUERY_FORMATTED` and `GET_HOVER_INFO` messages to its worker: ad-hoc messages, not LSP. No hosted
  playground with editor features was found.
- **Gleam**: the language tour runs the Wasm compiler in a worker (`website.md` 3.2). It has no hover
  or completion; the editor is CodeFlask.

### 3.6 CodeMirror 6

- `@codemirror/view`: `hoverTooltip(source, { hoverTime = 300, hideOnChange })` takes an async source
  for a position and is **mouse-only** (it reacts to `mousemove`). `showTooltip` is a facet for tooltips
  driven by state, such as the cursor, which is the documented way to show one from the keyboard.
- `@codemirror/autocomplete` 6.20.3: async completion sources, `validFor` (keep filtering locally while
  the typed text still matches), abort on new input, and keyboard (Ctrl-Space, arrows, Enter, Escape).
  It sets ARIA `aria-autocomplete`, `aria-expanded`, `aria-controls` and `aria-activedescendant`.
- `@codemirror/lsp-client` 6.2.2: hover, completion, definition (F12), references (Shift-F12, with a
  panel), rename (F2), signature help and formatting over any `Transport` (a send/subscribe pair, so a
  worker would do). It depends on `marked` and on `vscode-languageserver-protocol`.

### 3.7 Comparison

| | where it computes | when | protocol | hover | definition | references | completion | fixes | keyboard hover | touch | client weight |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Verso (Lean manual) | build | build time | static HTML and site-wide JSON | yes | links | occurrence highlight | – | – | no | tap (tippy) | tippy + popper + marked, ~70 KB min |
| lean4web | server | live | LSP over WebSocket | yes | yes | yes | yes | yes | Monaco | partial | Monaco, React, VS Code layer |
| Rust Playground | server | on Run | HTTP | no | no | no | crate names only | no | – | – | Ace or Monaco, React |
| Scastie | server (Metals) | live, per request | HTTP, whole document per request | yes | no | no | yes | no | no | – | CodeMirror 6, Scala.js, marked |
| Koka playground | browser worker (Wasm) | live | LSP via SharedArrayBuffer | yes | yes | – | yes | – | Monaco | – | Monaco, React, COI service worker |
| Roc web REPL | browser worker (Wasm) | live | ad-hoc messages | being added | no | no | no | no | – | – | none |
| Gleam tour | browser worker (Wasm) | on edit | ad-hoc messages | no | no | no | no | no | – | – | CodeFlask |
| **Hugin, proposed** | browser worker (Scala.js) and build | table after a pause in typing, requests for cursor features; build time for the reference | ad-hoc messages (5); static HTML and per-page JSON | yes | yes, and library names link to the reference | occurrence highlight, Shift-F12 | yes | yes, and the meta actions | yes (info bar, Ctrl-K Ctrl-I; roving focus in the reference) | yes | +9 KB gzip in the playground; ~3 KB script in the reference |

What the references agree on: **build-time hovers are static spans plus a deduplicated table** (Verso).
**Live features in the browser are the language server's own code in a worker** (Koka), but the LSP
wire format is not needed between a page and its own worker. Roc and Gleam use ad-hoc messages, and
Hugin's worker already does (#145). No reference gives keyboard access to build-time hovers; Hugin
should (9).

## 4. The shared core: `hugin.ide`

### 4.1 What moves

Everything that decides *what* the editor shows moves into `hugin.ide`; everything that decides *how it
is encoded* stays in `hugin.lsp`. All `hugin.ide` functions take a `CompileKey` or a path and an offset,
and return case classes with `Span`s.

| from | to `hugin.ide` | stays in `hugin.lsp` |
|---|---|---|
| `Features.hover`, `MetaFeatures.hover` | `Hover.at(key, off): Option[Hover(signature: Option[String], notes: List[String])]`, with the merge, the deduplication and the between-tokens rule | the Markdown (a fenced `hugin` block, then the notes), `MarkupContent` |
| `Features.definition`, `references` | `Navigation.definition(key, off): Option[Target]`, `Navigation.references(key, off, includeDeclaration): List[Span]`; `Target` is `InFile(span)` or `Library(module, name)` (new: today a library declaration answers nothing) | `Location` with URIs; `Library` targets give no location, as today |
| `Features.completion`, `MetaFeatures.expected`, `MetaFeatures.inQuote`, `isObjectKind`, `completionTriggers` | `Completion.at(key, off): Completions(from: Int, items: List[Candidate(label, kind: CandidateKind, detail, fits: Boolean)], ranked: Boolean)`, `Completion.triggers`; `CandidateKind` is an enum, replacing the strings | `CompletionItemKind`, `sortText`, `preselect` |
| `Features.codeActions`, `workspaceEdit`'s library filter, `MetaFeatures.codeActions`, `splitAction`, `action` | `Fixes.at(key, path, from, to): List[Fix(title, kind: FixKind, edits: List[Edit(span, text)], preferred, diagnostic)]`; `FixKind` is `QuickFix` or `Rewrite` | `CodeAction`, `WorkspaceEdit` with URIs, the diagnostic's LSP form |
| `Features.documentSymbols`' nesting | `Outline.of(key): List[Node(symbol, extent, children)]` | `DocumentSymbol`, `SymbolKind` |
| `MetaFeatures.inlayHints`, `HintSettings` (case class, `kinds`) | `Hints.in(key, path, from, to, settings): List[Hint]` | positions, `InlayHintKind`; `HintSettings.from(JsonObject)` stays |
| `MetaFeatures.goalData` | `Goals.at(key, span): Option[Goal]` (the record `MetaIde.goalAt` returns) | the gson `JsonObject` of the diagnostic's `data` |
| `MetaFeatures.expansion`, `codeLenses` | `Expansions.at(key, off): Option[String]`, `Expansions.sites(key, path): List[(Span, Int)]` | `CodeLens`, `Command`, `ExpansionCommand`, `positionArgs` |
| `Features.fileDiagnostics` (the crash guard), `isFacts` | `Diagnostics.of(key)`, `Files.isFacts` | publishing by URI, `toLsp`, severities, `codeDescription` |
| documents (`update`, `close`, `changedOnDisk`) | – (the database's `SourceText` input is already the shared part) | the open-document map with the client's URIs |

About 300 lines move. `Features` and `MetaFeatures` shrink to about 220 lines of encoding, and every
LSP method becomes "convert the position, call `hugin.ide`, encode the result". `hugin.query.Ide`,
`MetaIde` and `Expansion` stay where they are: they are the compiler's queries, used by the REPL and
`hugin ide` as well, and `hugin.ide` is the editor layer above them. A side benefit is that `hugin ide
hover` (in `cli/Main.scala`) can call `hugin.ide.Hover` and show the meta notes the LSP shows, which
it misses today.

The 11 LSP goldens (`tests/lsp/*.check`: hover, navigation, completion, fixes, hints, holes, expansion,
tokens) must stay byte-identical. That is the test that the move changes nothing.

### 4.2 Offsets, not positions

`hugin.ide` uses offsets into the file's text. JVM strings, Scala.js strings (JavaScript strings) and
CodeMirror documents all index UTF-16 code units, so an offset from the compiler is a CodeMirror
position as it is. That holds when the editor's text is exactly the text compiled, which the protocol
guarantees by versions (5.2). Only the LSP converts to lines and characters (`Positions`). The existing
JSON diagnostics keep their 1-based lines and columns (format version 1, shared with the CLI); new
messages use offsets.

### 4.3 The annotation table

`hugin.ide.Annotations.of(key, path): Annotations` is the bulk form of hover and navigation for a whole
file:

```scala
final case class Annotations(
    names: List[Annotated],   // sorted, non-overlapping: every name the semantic index knows
    hovers: Vector[Hover],    // deduplicated; Annotated.hover indexes it
    hints: List[Hint])        // the inlay hints (default settings), for the playground only
final case class Annotated(span: Span, hover: Int, target: Option[Target], group: Int, declaration: Boolean)
```

`group` numbers the occurrences of one symbol or object variable, so references and occurrence
highlighting are a filter on it. It is computed from the semantic index in one pass: references and
symbols grouped by span, then `Hover.at` per distinct target. It does not call `Ide.targetAt` per
token, since that scans all references each time. The same function serves:

- `hugin highlight --info` at build time (7);
- the worker's `analyse` answer (5), from which the playground answers hover, definition, references
  and occurrences locally (6.1);
- tests, as a golden of a file's annotations.

## 5. The worker protocol

### 5.1 One session, persistent

The worker keeps **one `Database` for its lifetime** (a `hugin.web.Session`), with the program as the
`SourceText` input of `main.hgn`. A request that carries the same text as the last one reuses the
memoized `Compile`. `Database.set` starts no new revision for an equal value, and early cut-off spares
dependents. So `analyse` after `check`, `complete` after `analyse`, and repeated requests at one version
cost no compilation. A worker restarted after the budget starts a new session, as today.

### 5.2 Messages

Every request carries `version`, a counter the page increments on each document change, and the
`source` of that version. Sending the text every time keeps the worker stateless across restarts, and
programs are small; the database makes it free when unchanged.

```
page → worker                                                        worker → page
{ id, op: "run" | "check", version, source, printAfter }           { id, result: { …as today…, version, info } }
{ id, op: "analyse", version, source }                             { id, result: { version, tokens, info } }
{ id, op: "complete", version, source, offset }                    { id, result: { version, from, items: [{ label, kind, detail, fits }] } }
{ id, op: "actions", version, source, from, to }                   { id, result: { version, actions: [{ title, kind, preferred, edits: [{ from, to, insert }] }] } }
{ id, op: "expansion", version, source, offset }                   { id, result: { version, text } }      (text: null if none)
```

`info` is the annotation table (4.3) in JSON:

```json
{ "names": [[from, to, hover, group, flags, target], …],
  "hovers": [["rel path : node -> node -> rel", "note…"], …],
  "hints": [[at, "label", "tooltip", kind], …] }
```

`flags` bit 0 marks a declaration. `target` is absent, an offset (the declaration's start in the
program) or `["std/graph", "tc"]` (a library declaration). A hover is its signature followed by its
notes. Offsets are UTF-16, as CodeMirror's.

`analyse` replaces `highlight`: the same idle trigger, plus the table. `run` and `check` return the table
too, so a check refreshes everything at once.

### 5.3 Staleness and ordering

- The worker answers in order, one request at a time, as today.
- The page drops an answer whose `version` is not the editor's current version, which generalizes
  #145's "same source" test. Completion relies on `@codemirror/autocomplete`'s own abort as well.
- The annotation table stays valid across edits the way the semantic tokens do: its ranges are a
  CodeMirror `RangeSet` mapped through each change, and a range an edit touches is dropped. Hovering
  untouched code keeps working while the reader types, and the next `analyse` replaces the table.
- While a run or check is busy, the page sends no IDE requests (as `highlightSoon` does now). Completion
  then offers nothing rather than queueing behind a long run, and hover keeps working from the table.
- The 10 s budget applies to every request. An IDE request that hits it (a meta program whose
  elaboration is the expensive part) stops the worker, as a highlight would today.

## 6. The playground

### 6.1 Features

| feature | source | CodeMirror | keys |
|---|---|---|---|
| hover | table | `hoverTooltip` (mouse, 300 ms) | Ctrl-K Ctrl-I at the cursor (`showTooltip` state field) |
| info bar | table | a one-line `showPanel` under the editor: the signature at the cursor, and "Definition" if there is one | follows the cursor |
| go to definition | table | moves the selection and scrolls; a library target opens the reference's page for the module in a new tab | F12, Ctrl/Cmd-click |
| occurrences | table (`group`) | marks on every occurrence of the name at the cursor (as Verso's `binding-hl`) | – |
| references | table | the occurrences as a small panel listing their lines; Enter jumps | Shift-F12, Escape closes |
| completion | `complete` | `autocompletion` with an async source; `validFor: /^[\w']*$/` filters locally; candidates that fit the expected type first | Ctrl-Space, or typing; also after `.`, `{` and `%` |
| quick fixes | diagnostics (today) and `actions` | the lint actions and inline buttons stay; Ctrl-. opens a menu of the actions at the cursor (split, add the missing clauses, add a clause, refine a hole, and the suggestions) | Ctrl-. |
| inlay hints | table (`hints`) | widgets, off by default, switched in the toolbar | – |
| expansion | `expansion` | an "Expansion" tab in the results pane, filled for the directive or functor application at the cursor | from the Ctrl-. menu ("Show expansion") |

Rendering: a hover's signature is shown as code with the playground's highlighting classes; its notes
are text in which `` `…` `` spans become `<code>`. Hugin has no doc comments, and the hover texts are
the compiler's own, so no Markdown library is needed.

### 6.2 Code shape

`editor.js` gains one module, `ide.js` (about 250 lines): the table's state field, the hover source, the
info bar, the keymap and the references panel. Completion and actions are thin async sources calling
`request()` in `main.js`. `worker.js` forwards the new ops. On the Scala side, `hugin.web.Session` (the
persistent database) and the JSON encoders of `info`, completions and actions (about 120 lines) call
`hugin.ide` only.

## 7. The reference

### 7.1 Build

`reference/highlight.py` calls `hugin highlight --info`. The input is unchanged (snippets
`{ code, prelude }`). Each output element becomes `{ "runs": [[text, [class, …], name?], …],
"names": [{ "hover": n, "group": g, "decl": bool, "target": … }], "hovers": [[sig, note, …], …] }`, where
a run's third element indexes `names`. Without `--info` the output stays as today, so `site/build.mjs`
is unaffected.

### 7.2 HTML

The preprocessor numbers the page's blocks, merges and deduplicates the hover texts of all blocks of
the page into one table, and writes:

```html
<pre><code class="hugin hljs nohighlight" data-hg="3" tabindex="0" aria-label="Hugin code, arrow keys move between names">
<span class="hg-function hg-declaration" data-i="12" id="hg3-path">path</span> X Y :- …
<a class="hg-function" data-i="12" href="#hg3-path" tabindex="-1">path</a> …
<a class="hg-namespace hg-defaultLibrary" data-i="31" href="std/graph.html" tabindex="-1">tc</a> …
</code></pre>
…
<script type="application/json" id="hg-hovers">[["rel path : node -> node -> rel"], …]</script>
```

- `data-i` indexes the page's table. Occurrence groups are the same `data-i` with the same `href`
  inside one block, so no extra attribute is needed.
- A use links to its declaration's `id` in the same block. Each block is its own program, so links
  never cross blocks. A library name links to the module's page in the reference (`std/graph.html`,
  `prelude.html`), with an anchor to its row where the page's declaration table lists the name. The
  preprocessor finds those anchors from the tables' first code spans and adds the `id`s.
- Links have `tabindex="-1"`: the block is the single tab stop (9.1). Without JavaScript, mouse and touch
  users still follow links.
- The table holds plain strings and is read with `JSON.parse`; it is never inserted as HTML.

### 7.3 Script and style

`reference/hugin-info.js` (about 120 lines, ~3 KB minified, ~1.3 KB gzip, loaded with mdBook's
`additional-js` and `defer`) creates one popup element, positions it under or over the token with
`getBoundingClientRect` (flipping at the viewport edge, `max-width: min(36rem, 100vw - 2rem)`), and
handles mouse (300 ms delay; the popup is interactive so its "Definition" link can be clicked), focus and
keys (9.1), and touch (9.2). `hugin.css` gains about 1 KB: the popup, the occurrence highlight, and a
focus ring for the current name. Both use the reference's existing palette in light and dark.

Why not CSS-only (`:hover`/`:focus-within` on a nested hidden span), which #132 offered as an option:

- the popup would be clipped: a `<pre>` scrolls horizontally (`overflow-x: auto`), which clips
  absolutely positioned children, and CSS anchor positioning is not yet available in every browser;
- `:focus-within` needs every name to be focusable, which means hundreds of tab stops on a page
  (`reflection.md`: about 690 occurrences);
- the text would repeat at every occurrence instead of once per page. Gzip absorbs that (7.4: inline
  popups came out 5–15 % *smaller*), so this is not a reason, but the raw HTML a screen reader or a
  copy-and-paste meets would hold every hover text inside the code;
- iOS keeps `:hover` stuck after a tap, with no way to close the popup.

### 7.4 Size budget

Measured with a scratch program over the reference's pages (13), which computed every name's hover
text as the LSP does (`Ide.hoverInfo` and `MetaIde.hover`, merged).

The program compiled every `hugin` block of `reference/src` as `hugin highlight` does and took the
hover text at every semantic token. It then rendered the annotated tokens three ways: plain spans (the
baseline), spans with `data-i` plus the page's deduplicated JSON table (7.2), and spans that each
contain a hidden popup with the full text (CSS-only). The figures are the bytes added over the
baseline after gzip at its default level (the bundle figures in 8 use level 9, as `site/build.mjs`).

| page | blocks | tokens | with hover | distinct hovers | table, raw JSON + attributes | **table, gzip added** | inline popups, gzip added | library names |
|---|---|---|---|---|---|---|---|---|
| `reflection.md` (largest) | 17 | 725 | 686 | 341 | 55.7 KB | **4.7 KB** | 4.4 KB | 72 |
| `std/list.md` | 17 | 248 | 229 | 166 | 30.9 KB | **3.0 KB** | 2.6 KB | 76 |
| `std/directives.md` | 14 | 403 | 366 | 173 | 38.5 KB | **3.0 KB** | 2.7 KB | 90 |
| `modules.md` | 13 | 362 | 349 | 172 | 36.7 KB | **3.0 KB** | 2.8 KB | 26 |
| `object/types.md` | 16 | 329 | 308 | 172 | 26.4 KB | **2.8 KB** | 2.6 KB | 16 |
| `object/rules.md` (typical) | 4 | 97 | 97 | 54 | 8.6 KB | **0.9 KB** | 0.8 KB | 9 |
| median of the 33 pages | | | | | | **0.8 KB** | | |
| all 33 pages | 183 | 4 938 | 4 754 | | | | | |

Gzip removes the repetition of inline popups almost entirely, so size is *not* an argument for the table
over CSS-only (7.3 gives the arguments that are). The links and anchors of 7.2 are not included above and
should add about a third. The scratch program took 10.3 s on the JVM for all pages, compilation
included, with a per-token lookup that the one-pass table of 4.3 avoids.

Budget: the added bytes (attributes, links, anchors and the JSON table), gzip, are **at most 8 KB per
page**, which leaves ~40 % headroom over the largest page today (4.7 KB plus links). A typical page adds
about 1 KB. `highlight.py` prints the largest page's figure, and the
reference workflow fails above the budget, as `site/build.mjs` reports the playground's sizes today. The
script and CSS (~2.5 KB gzip together) are cached once for the whole book.

## 8. Bundle size and latency

### 8.1 Playground bundle (`play.js`)

Measured with esbuild 0.28.2 (minified, ES module, the build's settings) on the playground's current
`main.js`:

| variant | minified | gzip | added gzip |
|---|---|---|---|
| today (view, state, commands, language, lint) | 342.2 KB | 111.4 KB | – |
| + `hoverTooltip`, `@codemirror/autocomplete` 6.20.3 and its keymap | 369.5 KB | 120.5 KB | **+9.1 KB** |
| + `@codemirror/lsp-client` 6.2.2 with `languageServerExtensions()` | 440.9 KB | 142.7 KB | +31.3 KB |

`ide.js` itself adds an estimated 3 KB gzip.

### 8.2 Compiler bundle (`hugin.js`)

The facade today reaches only compilation, evaluation and highlighting, so the linker drops `Ide`,
`MetaIde` and `Expansion`. Linking them in, measured by a scratch facade that calls every query the
features use:

| bundle | minified | gzip | added gzip |
|---|---|---|---|
| `hugin.js` today (Closure, `fullLinkJS`) | 2 095.7 KB | 536.3 KB | – |
| + every query the features use (`Ide`, `MetaIde`, `Expansion`: hover, definition, references, completions, symbols, hints, split, skeleton, goals, expected types, expansion) | 2 125.2 KB | 544.4 KB | **+8.1 KB (1.5 %)** |

The feature layer of 4.1 adds little on top: it is the decision logic over these queries. Together with
8.1, the playground's download grows by about 20 KB gzip, from about 650 KB to about 670 KB. The bundle is
cached after the first visit.

### 8.3 Latency

| step | expected | why |
|---|---|---|
| hover, definition, occurrences, references | one frame (no worker round trip) | from the table on the main thread |
| table after typing stops | 400 ms idle + one warm compilation (tens of ms for the examples, `website.md` 2.2) + the table (a few ms) | as the highlighting today; the table adds a pass over the index |
| completion, first keystroke | one compilation if the text changed since the last `analyse`, then the candidates: under 100 ms for the examples | the persistent database (5.1) |
| completion, later keystrokes | none | `validFor` filters locally |
| actions, expansion | as completion | on explicit request only |
| cold start | unchanged (~140 ms load, ~0.5 s first compilation) | – |

Programs as heavy as `bench/meta/meta_scaled.hgn` (seconds per compilation) get stale tables while the
reader types, as they get stale colours today. The page never waits for them.

## 9. Accessibility

### 9.1 Keyboard

- **Reference:** each code block is **one tab stop** (`tabindex="0"`, with an `aria-label` that names the
  keys). While it has focus, ArrowRight and ArrowLeft move a roving focus to the next or previous name,
  Home and End to the first and last. The block scrolls to keep the name visible, which replaces arrow
  scrolling of the `<pre>`. The focused name shows its popup. Enter follows its link, and Escape hides
  the popup and returns focus to the block. Tab leaves the block. This is the composite-widget
  pattern of the ARIA authoring practices (roving `tabindex`). It keeps a page with hundreds of names
  navigable, where links as tab stops would not. The focused name points at the popup with
  `aria-describedby`, and the popup has `role="tooltip"`, so screen readers read the hover text
  with the name.
- **Playground:** CodeMirror's hover tooltip is mouse-only, so the same information is available
  three ways: the **info bar** (it follows the cursor and is not a live region, so it does not chatter);
  **Ctrl-K Ctrl-I**, which opens the tooltip at the cursor and announces it through a polite live region;
  and F12 and Shift-F12 for definition and references. Completion and the Ctrl-. menu are listboxes
  with CodeMirror's ARIA attributes. All bindings are listed in a "Keys" note under the editor.

### 9.2 Touch and small screens

- **Reference:** where `(hover: none)` matches, the first tap on a name shows its popup instead of
  following the link. The popup has a "Definition" link, and a tap outside or on the same name closes
  it. The script listens to `click`, which a scrolling swipe does not fire, so horizontal scrolling of a
  code block stays free. Popups never exceed the viewport's width minus 2 rem. Tap targets in the popup
  are at least 44 px high.
- **Playground:** a tap moves the cursor, so the info bar shows the name's signature and a
  "Definition" button. That is the touch path, with no long-press gestures. Completion is CodeMirror's
  (it works with on-screen keyboards). The Ctrl-. menu also opens from a "Fix" button in the info bar
  when actions exist at the cursor.

### 9.3 Other

Popups follow `prefers-reduced-motion` (no fade). The palette's contrast is that of the existing code
colours. Nothing depends on colour alone: the occurrence highlight is a background plus an underline.

## 10. Alternatives rejected

- **`@codemirror/lsp-client` over a worker transport.** It would need the worker to speak LSP JSON-RPC.
  lsp4j is JVM-only, so that is a second, hand-written LSP encoder in `web`, duplicating `hugin.lsp`.
  It also costs +31 KB gzip including marked, and its hover is per-request. The table answers hover
  without a request.
- **Running `HuginLanguageServer` in the worker** (Koka's route). Same lsp4j problem; Koka also needs
  `SharedArrayBuffer`, and so cross-origin isolation through a service worker, on a static host.
- **Hover by request** (Scastie, lsp-client). Each hover would be a round trip that waits behind a
  busy run. Small programs make the table cheap, and the table is the format #132 needs anyway.
- **A second worker for IDE requests while a run is busy.** It doubles memory and start-up for a
  case the table already covers (hover keeps working). It can come later if completion during long runs
  matters.
- **tippy.js, popper.js and marked in the reference** (Verso). About 70 KB minified for what one
  positioned element and a backtick rule do.
- **A site-wide hover table** (Verso's `-verso-docs.json`). It is one extra fetch, grows with the
  whole book, and needs care with caching. A per-page inline table is smaller for any one page and
  needs no request.
- **CSS-only popups** (7.3).
- **Hovers on the landing page.** It would be the first JavaScript on the landing page beyond the
  theme switch. "Open in the playground" is one click away (12, question 3).

## 11. Batches

One PR per batch. Sizes are changed lines including tests.

| batch | issue | content | depends on | size |
|---|---|---|---|---|
| **I1** feature layer | #147 (prerequisite of #132) | move hover, navigation, completion, fixes, outline, hints, goals, expansion and the diagnostics guard into `hugin.ide` (4.1); `Features`/`MetaFeatures` become encoders; `hugin ide hover` uses `hugin.ide.Hover`; unit tests in offsets; the 11 LSP goldens unchanged; the web project compiles `hugin.ide` in CI | – | M: ~300 moved, ~80 new Scala, ~150 tests |
| **I2** annotation table | #132, #147 | `hugin.ide.Annotations` (4.3), with library targets; `hugin highlight --info` (7.1); goldens for a few snippets, one per kind of name (relation, constructor, meta function, functor, library name, object variable) | I1 | S–M: ~150 Scala, ~120 tests |
| **R1** reference hovers | #132 | `highlight.py` (anchors, links, `data-i`, per-page table, std anchors, budget check), `hugin-info.js`, CSS, `additional-js` in `book.toml`; a Node or Playwright smoke test of keyboard and tap behaviour in the reference workflow | I2 | M: ~120 Python, ~150 JS, ~60 CSS, ~40 CI |
| **P1** session, table, hover and navigation | #147 | `hugin.web.Session` (persistent database), `analyse` and `info` in `run`/`check` (5); `ide.js`: hover, info bar, Ctrl-K Ctrl-I, F12, Ctrl-click, occurrences, Shift-F12 panel; the bundle sizes in the build log | I2 | M: ~120 Scala, ~300 JS/CSS |
| **P2** completion | #147 | `complete` op, `@codemirror/autocomplete` (+9 KB gzip), triggers, ranking | P1 | S: ~40 Scala, ~80 JS |
| **P3** actions | #147 | `actions` op, Ctrl-. menu and the info bar's "Fix" button | P1 | S: ~50 Scala, ~100 JS |
| **P4** hints and expansion | #147 (judged separately, as both issues say) | inlay hints from the table with a toolbar switch; `expansion` op and the "Expansion" tab | P1 | S: ~30 Scala, ~120 JS |

I1 can land now; it touches only `lsp/` and the new `ide/` files. After I2, R1 and P1 are independent
and can go in either order. Per #132's comment, the reference work was queued after the website's
W4/W5, which have landed.

## 12. Open questions

1. **Hover content: structured strings or Markdown?** The LSP sends Markdown. The web needs a
   signature and notes. *Recommendation:* `hugin.ide.Hover` stays structured (signature, notes); the LSP
   builds its Markdown from it, and the web renders backtick spans only. No Markdown library on the
   site.
2. **Reference keyboard model: roving focus (block = one tab stop) or every name a link in the tab
   order?** *Recommendation:* roving focus (9.1). Verso has no keyboard access at all, and tab stops per
   name would make long pages tedious.
3. **Hovers on the landing page's example?** *Recommendation:* no, for now. It keeps the landing page free
   of JavaScript beyond the theme switch (#58). The example links to the playground. The renderer
   would allow it later with one script tag.
4. **Where do library names link?** The reference's module page, or the library's source on GitHub?
   *Recommendation:* the reference page (with a row anchor where the declaration table lists the name),
   so the reader stays in the reference and the link does not depend on a commit.
5. **Table or per-request hover in the playground?** *Recommendation:* the table (4.3), for latency,
   for hover while a run is busy, and for one code path with #132.
6. **One worker or a second one for IDE requests?** *Recommendation:* one; revisit only if completion
   during long runs is missed (10).
7. **Inlay hints, typed-hole goals and the expansion in the reference?** #132 lists them as "maybe
   later, judged separately". *Recommendation:* not in R1. Goals are already in the diagnostics that the
   error index shows. Revisit after R1 with real pages.
8. **Should the budget check fail the build or only report?** *Recommendation:* fail above 8 KB gzip
   per page, like the other checks of the reference build, so growth is a decision rather than drift.
9. **Should `hugin.query.Ide` and `MetaIde` move into `hugin.ide` too?** *Recommendation:* no. They are
   compiler queries, used by the REPL and the CLI. Moving them would grow I1's diff without changing
   what the browser can do.
10. **Documentation in hovers** (#147: "types and documentation")? Hugin has no doc comments, so
    hovers show signatures and the compiler's notes. *Recommendation:* out of scope; doc comments
    would be a language change with its own issue.

## 13. Sources

Clones are shallow, made on 2026-10-10.

- Verso: `leanprover/verso` at `51de83d`: `src/verso/Verso/Code/Highlighted.lean` (`Hover.Dedup`,
  `addHover`, `data-verso-hover`, `fetchDocsJson`, `highlightingJs`, the tippy options, the CSS),
  `src/verso/Verso/Code/Highlighted/WebAssets.lean`, `src/verso-manual/VersoManual.lean`
  (`-verso-docs.json`), `doc/UsersGuide/Output/HTML.lean`, `vendored-js/` (tippy and popper sizes).
- SubVerso: `leanprover/subverso` at `892d6dc`: `src/SubVerso/Highlighting/Highlighted.lean`.
- lean4web: `leanprover-community/lean4web` at `9c4cd4f`: `README.md`, `server/index.mjs`,
  `client/package.json`.
- Rust Playground: `rust-lang/rust-playground` at `493c31b`: `ui/frontend/editor/MonacoEditorCore.tsx`,
  `AceEditorCore.tsx`.
- Scastie: `scalacenter/scastie` at `073a9c4`: `build.sbt` (`metalsRunner`),
  `client/src/main/scala/org/scastie/client/components/editor/MetalsClient.scala`, `MetalsHover.scala`.
- Koka: `koka-lang/koka` at `9c55695`: `web/playground/PLAYGROUND.md`, `web/playground/src/`.
- Roc: `crates/repl_wasm/README.md` and the commits adding `QUERY_FORMATTED` and `GET_HOVER_INFO`
  (mirror at git.joshthomas.dev/language-servers/roc); no hosted playground found.
- Gleam: `gleam-lang/language-tour` at `234cb02` (no hover or completion in `static/`).
- CodeMirror: `codemirror/lsp-client` at `97bb453` (6.2.2: `src/hover.ts`, `definition.ts`,
  `references.ts`, `package.json`); npm `@codemirror/view` 6.43.14, `autocomplete` 6.20.3, `lsp-client`
  6.2.2, bundled with esbuild 0.28.2.
- Hugin at `a1a4274`: `src/main/scala/hugin/lsp/`, `hugin/ide/`, `hugin/query/Ide.scala`, `MetaIde.scala`,
  `Expansion.scala`, `Database.scala`, `cli/Highlight.scala`, `cli/Main.scala`, `web/src/main/scala/hugin/web/`,
  `site/play/`, `site/build.mjs`, `reference/highlight.py`, `reference/book.toml`, `tests/lsp/`,
  `docs/design/website.md`.
