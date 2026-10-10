# A website with an in-browser playground

Design note for [issue #58](https://github.com/k0uks1/hugin/issues/58): a small site for Hugin with a
landing page and a playground that runs the compiler in the browser. Status: round 2. The designer approved
the recommendations and the open decisions of round 1, and asked for a more polished visual design
(4.11). Nothing is implemented. The static prototype is in `site/` (`index.html`,
`play/index.html`, `style.css`). The experiments this note cites were run against `bf14ffb` in a scratch
copy and are not committed.

The issue's base restrictions are binding and apply to every batch: the site is not a marketing site
(no pitch, no persuasive copy, no superlatives, testimonials or feature sections), and it is simple
and fast: static pages, no JavaScript outside the playground, no tracking or cookies, no framework, system
fonts, light and dark mode.

Contents: 1 recommendations, 2 Hugin today, 3 prior art, 4 assessments, 5 alternatives rejected,
6 batches, 7 sources.

## 1. Recommendations

1. **Scala.js with the JavaScript backend.** A throwaway build that compiled `src/main/scala` without
   `cli`, `repl` and `lsp` for Scala.js linked after five small changes (section 2.2). The bundle ran all
   79 single-file `tests/run` programs with output identical to the JVM, after accounting for the tests'
   `.flags` options. The minified bundle (Closure) is **1.9 MB, 485 KB gzip, 371 KB brotli**.
2. **Wasm later, if measurements justify it.** Scala.js 1.21.0's WebAssembly backend works in Chromium 141.
   It is 2.9 MB (858 KB gzip), about 1.8 times the JS download. Warm runs of small programs are about
   twice as fast, and the largest benchmark is 10–25 % faster. Scala.js 1.17.0 and 1.19.0 produced Wasm that
   Chromium and Node 22 rejected. Ship JS first and reconsider Wasm when evaluation time, rather than
   download size, is what users wait for (4.1).
3. **No language change.** The compiler runs unchanged apart from replacing two JVM-only libraries, hiding
   file IO behind an interface and one `String.codePoints` call. No batch touches the language, the
   reference or the diagnostics.
4. **Sequence the build changes around the open feature branches.** First, small in-place PRs: replace the
   dependencies, then add the IO interface. Then one mechanical PR, at a quiet moment, that moves the
   sources into a `crossProject` layout and changes nothing else. A no-move variant that lets the
   playground ship before the move is described in 4.3.
5. **URL layout: landing at `/hugin/`, reference at `/hugin/reference/`, playground at `/hugin/play/`.**
   Every old reference URL gets a static redirect page, and `reference/site-url.txt` changes in the
   same PR. Approved; the alternative was keeping the reference at the root (4.5).
6. **Site: hand-written HTML and one CSS file.** A short build script inserts the checked example and
   its output and highlights them at build time with the compiler, as the reference does. The landing
   page loads 5.5 KB gzip (HTML and CSS) and no JavaScript. The visual design follows lean-lang.org
   (4.11).
7. **Playground: CodeMirror 6, a highlighter generated from the VS Code grammar, the compiler in a Web
   Worker.** Cancel terminates the worker. Diagnostics come from the existing JSON format, answers are
   shown as tables, and sharing uses a compressed program in the URL fragment. The examples are the
   reference's `hugin,run` blocks.

## 2. Hugin today

### 2.1 Measurements

On `bf14ffb`, `src/main/scala` has 194 files (26 346 lines). Of these, 181 files (24 431 lines) would
form `core`. The other 13 files (1 915 lines) are the JVM-only `cli`, `repl` and `lsp` packages, and no
core file imports them (checked by grep). The compiled `hugin_3-0.1.0.jar` is 6.6 MB: 2 151 class files
(9.6 MB uncompressed), 4.1 MB of TASTy and 97 KB of resources. With its runtime dependencies, the staged
launcher's classpath is about 19 MB: scala-library 5.9 MB, jline 1.4 MB, jgrapht 1.3 MB and scala3-library
1.25 MB are the largest.

JVM APIs in core, by Scala.js support:

| use | core files | Scala.js |
|---|---|---|
| `java.nio.file` (`Files`, `Path`) | `compiler/Libraries.scala` (reading imports, path resolution), `util/Source.scala` (`SourceFile.fromPath`) | **not supported**: needs the IO interface |
| `getResourceAsStream` | `compiler/Libraries.scala` (the stdlib), `util/diagnostics/Explanations.scala` (`site-url.txt`, `docs/errors`) | **not supported**: bundle as generated sources |
| jgrapht | `util/Graphs.scala`, one function, `shortestPath` (BFS), called from `obj/check/Stratify.scala`; SCCs and topological order are already pure Scala | **JVM-only**: ~20-line BFS |
| commons-text `LevenshteinDistance` | `core/elab/Names.scala`, `compiler/LazyStdlib.scala` (and `repl/Session.scala`, JVM) | **JVM-only**: ~15-line Levenshtein |
| `String.codePoints()` (`IntStream`) | `syntax/Trees.scala` (`Literal.quote`) | **not supported**: a `codePointAt` loop |
| `Thread.interrupted()` | `runtime/Engine.scala:330`, the cancellation check of the fixpoint loop | compiles, never true: use a cancellation hook (4.9) |
| `catch StackOverflowError` | `core/elab/MetaTooling.scala:43` | JS throws `RangeError`; it is still caught, since `NonFatal` matches the wrapped exception |
| `java.util.IdentityHashMap` | 9 files (`core/MemoKeys`, `Staging`, `Readback`, …) | supported |
| `synchronized`, `@volatile` | `compiler/StdlibCache.scala`, `LazyStdlib.scala`, `core/elab/Clauses.scala` | supported (no-ops) |
| `AtomicLong`, `AtomicInteger`, `ConcurrentLinkedQueue` | `core/elab/Clauses.scala`, `obj/Types.scala` | supported |
| regex (`replaceAll`, `split`) | 10 files; the patterns are `\s+`, `(#\d+)+$`, `(?m)^```(\w+) .*$` and literal splits | supported (JS `RegExp`; no lookbehind, possessive or atomic groups used) |
| `f"…"` and `.format` | 12 files | supported |
| `System.nanoTime` | `compiler/Compiler.scala` (phase timings) | supported |
| reflection | `syntax/Slices.scala` (`getClass ==`), `util/Graphs.scala` (`classOf`, for jgrapht only) | supported / removed with jgrapht |
| `FileOutputStream`, `FileDescriptor`, `System.in`, `CompletableFuture`, `java.net.URI` | `cli/`, `lsp/` and `repl/` only | stay JVM-only |
| fansi | `util/DiagnosticRenderer.scala` | cross-built (`fansi_sjs1_3`); the browser uses the uncoloured rendering |

### 2.2 The experiment

A scratch sbt project with `sbt-scalajs` and the core sources, with these changes:

- `Libraries.scala`: path resolution on strings (POSIX `normalize`, `parent`, `fileName`). The stdlib
  comes from a generated object `BundledStdlib` (5 files, 44 KB). Files outside the stdlib are absent.
- `Source.scala`: dropped `fromPath`. `Explanations.scala`: a constant URL and no explanation texts.
- `Graphs.shortestPath`: a BFS. `Names`, `LazyStdlib`: a Levenshtein function.
- `Trees.scala`: the `codePointAt` loop. `Engine.scala`: `Thread.interrupted()` replaced by a deadline
  check.
- A facade with `@JSExportTopLevel("run")` that does what `hugin run` does on one in-memory file and
  returns the output lines and the JSON diagnostics.

Only `String.codePoints` was reported by the linker. Everything else in the table above either links or
was removed with the changes.

| bundle | raw | gzip | brotli |
|---|---|---|---|
| JS, ES module, no Closure (1.17.0) | 6.25 MB | 842 KB | 553 KB |
| JS, script, Closure (1.17.0) | 1.89 MB | 481 KB | 368 KB |
| JS, script, Closure (1.21.0) | 1.91 MB | 485 KB | 371 KB |
| Wasm (1.21.0): `main.wasm` + loader | 2.96 MB + 16 KB | 859 KB | 598 KB |

Times in headless Chromium 141 on the session's container (4 cores, load average 7–8, so the
numbers are rough). They are three interleaved runs of each bundle, loaded from localhost:

| | JS (Closure) | Wasm |
|---|---|---|
| load and initialize the bundle | 135–153 ms | 120–190 ms |
| first run of the landing example (includes the prelude and `std/` elaboration) | 447–523 ms | 368–446 ms |
| later runs of the landing example | 44–65 ms | 23–35 ms |
| `bench/meta/meta_scaled.hgn` (241 lines, meta-heavy) | 2.6–4.5 s | 2.7–4.0 s |

For comparison, a cold JVM `hugin run` of the landing example took 4.5 s on the same machine, and of
`meta_scaled` 8.9 s. `meta_scaled`'s output is identical on the JVM, in JS and in Wasm (same MD5). The JS
bundle ran it with V8's default stack, the same as a worker's. This is the program whose deep meta
recursion overflowed a 1 MiB JVM stack before #88 (`docs/PERFORMANCE.md`).

The JSON diagnostics come out unchanged, for example W0002 with its two suggestions. The prototype's
inline diagnostic shows exactly that output.

## 3. Prior art

### 3.1 Lean 4: lean-lang.org and live.lean-lang.org

The issue's reference point. The page opens with one sentence ("Lean is an open-source programming
language and proof assistant that enables correct, maintainable, and formally verified code") and
a code sample, and each example links to the playground. The documentation lives under the same domain
(`/doc/reference/latest/`). The same page also has feature cards, a "Lean in Action" project gallery,
testimonials, sponsors and a news timeline. **These are exactly what restriction 1 excludes**, so Hugin
takes the first screen's shape (sentence, code, links) and nothing below it.

The web editor `lean4web` runs Lean **on a server** ("This is a web application running Lean 4
server-side"). Its client uses Monaco through `lean4monaco` and React (`client/package.json`). Programs
are shared in the URL fragment: `#code=` is plain text, `#codez=` is LZ-string-compressed, and `#url=`
loads a file. It writes whichever of `code` and `codez` is shorter (`doc/Usage.md`).

### 3.2 Gleam: the language tour

The closest analogue. The Gleam compiler, written in Rust, is compiled to WebAssembly and **runs in the
browser**. The `gleam-v1.17.0-browser.tar.gz` release holds `gleam_wasm_bg.wasm`, 4.87 MB (1.66 MB gzip,
measured). The tour starts one module worker (`static/worker.js`) that instantiates the compiler, writes
the stdlib modules into an in-memory project, compiles to JS, and evaluates the result with `import()` of
a data URL. Edits are debounced by 200 ms and compiled on every change. There is no cancel and no
budget, and a looping program blocks the worker. The editor is CodeFlask, loaded from jsDelivr.

### 3.3 Scastie and the Scala.js playgrounds

Scastie compiles and runs on **servers** (`sbt-runner`, `scala-cli-runner`, behind a `balancer`). Its
client is itself Scala.js, with CodeMirror 6 (`@codemirror/*` in `package.json`) and tree-sitter-scala
for highlighting. Scastie shows that Scala.js plus CodeMirror 6 is a working combination. It does not
show a compiler in the browser, since its compiler is scalac on the JVM. No Scala.js-compiled compiler of
Hugin's size was found to cite. Section 2.2 is the measurement instead.

### 3.4 Rust, Elm, Koka

- The **Rust Playground** runs **server-side**: "A React frontend communicates with an Axum backend.
  Docker containers are used to provide the various compilers". The container limits memory and "total
  compilation and execution time". The editor is Ace or Monaco (`ui/frontend/package.json`). Sharing goes
  through GitHub gists.
- **Elm**'s "Try Elm" compiles on a **server**. A community answer notes that "The Try Elm! and all other
  solutions I've seen so far always communicate with a server" (discourse.elm-lang.org, "Online REPL for
  teaching").
- **Koka**: no official playground was found.

### 3.5 What the references agree on

Server-side playgrounds (Rust, Lean, Scastie, Elm) need a sandbox and an operator, so a static site cannot
host them. Hugin's compiler is pure computation and terminates on every input (evaluation of accepted
programs terminates, and meta functions are checked), so a client-side worker is enough. Gleam shows the
shape: compiler in a worker, stdlib bundled, results back as messages. Hugin adds the cancel that Gleam
lacks, because a terminating program can still be expensive. A ~0.5 MB gzip compiler is a third of
Gleam's download.

## 4. Assessments

### 4.1 Scala.js JS or Wasm

| | JS | Wasm |
|---|---|---|
| download | 485 KB gzip | 859 KB gzip |
| startup | ~140 ms | ~140 ms (streaming compile) |
| warm small program | 44–65 ms | 23–35 ms |
| heavy meta program | baseline | 10–25 % faster |
| maturity | stable since 2020 | experimental flag; 1.17.0 and 1.19.0 failed validation in current V8, 1.21.0 works |
| browsers | all | WasmGC and exception handling: current Chrome, Firefox and Safari |
| stack overflow | `RangeError`, caught | a trap; not verified whether `MetaTooling`'s catch sees it |
| linker options | Closure needs `NoModule` (a classic worker script) | ES module only, no Closure |

Choose JS. The user waits on the download once and on runs that already take tens of milliseconds, so
Wasm's speed gains do not pay for the 0.4 MB. Switching is a linker setting, so batch W6 re-measures on
realistic reference programs and switches only if Wasm is clearly faster without a larger download.

### 4.2 Expected bundle and startup

Over a 10 Mbit/s link, the compiler bundle (485 KB) arrives in about 0.4 s and CodeMirror (105 KB, 4.6)
in about 0.1 s. GitHub Pages serves gzip and has no brotli. The worker starts while the page loads, the
first run then takes ~0.5 s, and later runs take tens of milliseconds. The landing page loads none of
this. Bundle growth should be watched in CI (W4 prints the gzip size).

Two size reductions are left for later: the stdlib as generated strings (44 KB raw) and the 86
explanations (`docs/errors`, 348 KB raw). The explanations are not bundled: the playground links to the
error index instead.

### 4.3 Build layout and sequence

The target is an `sbt-crossproject` layout: `core` (JVM and JS: everything except `cli`, `repl` and
`lsp`), `cli` (JVM: the CLI, REPL and language server, depending on `core.jvm`) and `web` (JS: the
playground facade, depending on `core.js`). Platform code goes into `core/jvm` and `core/js`: file
reading and bundled resources. Tests stay on the JVM. `munit` is cross-built, but the golden suites read
files.

The move touches every source path, so it conflicts with every open branch. Hence the order:

1. **In place, small, any time:** replace jgrapht and commons-text, and fix `String.codePoints` (W1).
   This also drops about 2.9 MB from the launcher's classpath (jgrapht with jheaps and apfloat,
   commons-text with commons-lang3).
2. **In place, any time:** a `SourceFiles` interface for reading files and bundled resources. The JVM
   implementation is the current code. The pure path logic of `ImportPaths` stays on `java.nio` on the JVM,
   because Windows paths need it (W2). After this, all JVM-specific code is in two or three files.
3. **At a quiet moment, mechanical:** `git mv` into the cross layout plus `build.sbt`. Nothing else
   changes, so review is "same files, new paths" (W3). Branches opened after it rebase with
   `git rebase` rename detection.

**No-move variant.** Point the `web` project's `unmanagedSourceDirectories` at the existing
`src/main/scala`, and exclude `cli/`, `repl/`, `lsp/` and the two or three JVM platform files by
`excludeFilter`. It needs no file move, so the playground can ship before step 3. The cost is a less
obvious layout: a core file that imports `cli` breaks only the JS build, which CI catches. This note
recommends the move as the end state and allows the variant if step 3 has to wait.

### 4.4 Site generator

The reference is an mdBook (`reference/book.toml`, mdBook 0.5.4 in `reference.yml`, `hugin.css`). Options:

- **Hand-written HTML and CSS** (recommended). Two pages, one stylesheet (5.8 KB). The shared header is
  eight lines, copied. A ~60-line Node script (Node is needed for the playground bundle anyway) inserts
  the example and its output, highlights them with `hugin highlight` (4.7) into static spans, and
  writes `_site/`.
- **mdBook theme reuse.** It brings mdBook's JavaScript (sidebar, theme picker, search index) and the page
  chrome of a book. The landing page would look like a chapter. Rejected for the landing page. The
  reference keeps its theme.
- **A small generator** (Zola, Hugo, Eleventy). A third toolchain for two pages. Rejected.

The landing example must not drift. It is a file `site/example.hgn` with its expected output. CI runs it
like a `tests/run` golden: the build script fails if `hugin run` differs, and the example is added to
`GoldenTests`' inputs. The page text describes the language only in the one sentence, taken from the
README and consistent with the reference's introduction, and in the example's two comments. They match
the reference: `directives.md` ("User-defined directives", the same `%symmetric`) and `std/graph.md`
(`tc`: "its relation `path` is the transitive closure").

### 4.5 URL layout

Pages publishes one artifact per site, so the reference workflow becomes the site workflow: book into
`_site/reference/`, landing into `_site/`, playground into `_site/play/`.

- **Recommended:** `/hugin/` landing, `/hugin/reference/` book, `/hugin/play/` playground (with Lean's
  `/doc/reference/` as precedent). `site-url.txt` becomes `…/hugin/reference/`. This changes the error
  URLs printed by `hugin explain`, sent by the LSP and included in the JSON. It is one line plus the
  goldens that contain the URL (`tests/json/diagnostics.check`, `tests/repl/session.check`, six
  `tests/lsp/*.check`) and absolute links in `README.md`, `reference/STYLE.md`, `docs/NOTES.md` and some
  `docs/errors/*.md`. `reference/README.md` promises that `<site-url>errors/<code>.html` is stable. That
  promise is kept by static redirect pages at the old paths: mdBook's `[output.html.redirect]`, generated
  for every chapter and every error page by `error-index.py`. They use `<meta http-equiv="refresh">` and
  no JavaScript.
- **Alternative:** keep the book at `/hugin/` and replace only its `index.html` (a copy of the
  introduction, which stays at `introduction.html`) by the landing page. Nothing moves, but the book's own
  home link then leads to the landing page, and the site is a post-processed book. Rejected by the designer.

A custom domain is out of scope. It would change `site-url.txt` again.

### 4.6 Editor

CodeMirror 6, as the issue says. Bundled with esbuild (minified), measured on the current packages
(`@codemirror/view` 6.43, `state` 6.7, `language` 6.13, `lint` 6.9):

| setup | minified | gzip |
|---|---|---|
| view, state, commands (history), language (stream parser, bracket matching), lint with gutter, line numbers | 322 KB | 104 KB |
| `basicSetup` (adds search, autocomplete, folding, …) and lint | 398 KB | 129 KB |

Use the first setup. Monaco is several MB and is rejected in the issue. A plain `<textarea>` with an
overlay highlighter, as in Gleam's CodeFlask, is lighter, but it has no inline diagnostics, gutter or
undo history worth having. The editor bundle is self-hosted. Gleam loads CodeFlask from a CDN, which
would contradict "no third-party requests".

### 4.7 Highlighting

`editors/vscode/syntaxes/hugin.tmLanguage.json` (5 KB) uses `match`, `begin`/`end` with nesting (comments
and quote parentheses), `include`, `captures` and lookbehind. All of these exist in JS `RegExp`. A build
script compiles it to a CodeMirror `StreamLanguage` with a state stack: one grammar, two editors, no hand
port. The landing page's example is highlighted at build time by the compiler, as the reference's code
blocks are since #122. The build runs `hugin highlight` (the language server's semantic tokens) and
renders `hg-*` spans, which keeps the landing page free of JavaScript. `site/style.css` uses the
reference's palette (`reference/hugin.css`): the light colours of mdBook's light theme and tomorrow-night
for dark, so a program looks the same on the landing page and in the reference. The playground's
TextMate-based highlighter uses the same classes, so lexical colours match. Semantic colours (relations,
types and constructors told apart) appear in the playground after a check, from the compiler's tokens.

### 4.8 Diagnostics and results

- **Diagnostics:** the `web` facade returns the JSON of `JsonDiagnostics.encode` (version 1). Its spans
  are 1-based line and column, which map to CodeMirror lint ranges. `level` gives the severity, `code.url`
  links to the error index, and `rendered` fills a "Text" tab. A `MachineApplicable` suggestion becomes a
  lint action ("replace `D` with `_`").
- **Answers as tables:** today `Evaluation` returns rendered lines (`P = ann.`). The facade exposes the
  structured answers instead (query text, variable names, rows), and a "Relations" tab shows `%output`
  relations the same way. This is new JS-facing API in `web`, not a change of the compiler's output.
- **`--print-after`:** `Settings.printAfter` and `Compiler.phasePlan` exist. The "Show after" select
  lists the phases and shows the printed program read-only.
- **Imports:** `std/` modules work (bundled). Relative `%import` of a user's file is "cannot find"
  (E0108) in the first version. Facts files are not supported. Multi-file programs can come later as
  editor tabs, since the IO interface is the same.

### 4.9 Budget and cancel

The compiler runs in a dedicated worker started on page load. **Cancel calls `worker.terminate()`**,
which stops elaboration and evaluation alike, without the compiler's cooperation, and then starts a new
worker. The cost is a new start (~140 ms) and a cold first run (~0.5 s), since the stdlib cache is lost.
The **budget** is a main-thread timer, 10 s by default, that does the same and reports "stopped after
10 s". The fixpoint loop's existing check (`Engine.scala:330`) becomes a `Cancellation` hook. The JVM
implementation keeps `Thread.interrupted()`, and the JS implementation checks a deadline. Evaluation then
stops with the ordinary "evaluation cancelled" result just before the hard stop, and its diagnostics are
kept. There is no step budget in the first version: wall-clock time is what the user experiences, and
steps would need counters in the elaborator. A worker that runs out of memory is reported like a cancel.

### 4.10 Sharing

Share writes `#code=<base64url(deflate-raw(program))>` using the browser's `CompressionStream`, so no
library is needed, and `#example=<name>` for the reference examples. The fragment never reaches the
server, and there is no storage. A version prefix (`#v1:…`) is not needed: an unknown key is ignored and
the default example is shown. Lean's `codez` uses LZ-string. The built-in deflate saves the dependency.

### 4.11 Visual design

After the designer's first review, the design follows lean-lang.org more closely. Its stylesheets
(`-verso-data/layout.css`, `org-hero.css`, `card.css`, `navbar.css` and the page's inline variables) were
read on 2026-10-10. Hugin takes the following from it:

- **Hero:** two columns (text left, code right) in a container about 1 200 px wide, with a large bold
  title (3.4rem, tight letter-spacing) above a muted lede and two buttons. A faint radial glow sits
  behind the code. Lean uses a blurred blue radial gradient; Hugin's is a CSS gradient, with no image.
- **Code card:** white surface (dark grey in dark mode), 1px border, 14px radius, a layered soft
  shadow, a header bar that names the file, and the output as the card's footer.
- **Navigation bar:** sticky and translucent with backdrop blur, a hairline bottom border, and muted
  links with a soft hover background.
- **Section headings:** small uppercase, letter-spaced labels in the accent colour above a bold
  heading. Links become a four-column grid of cards (two on tablets, one on phones).
- **Palette:** a near-white blue-grey background (`#f8fafc`; Lean's is `#F9FBFD`), slate muted text and
  one blue accent. Dark mode is a refined near-black (`#111317`) with raised surfaces and a lighter
  accent (Lean: `#181818`, `#3b94ff`).

Not taken: web fonts (Lean loads Open Sans, Fira Code and Oranienbaum from Google Fonts; Hugin uses the
system stacks), reveal animations and their scripts, the theme-toggle script (Hugin follows
`prefers-color-scheme`), and the marketing sections (feature cards, testimonials, sponsors, timeline).
The papers are a list in one card, each with a small label naming the part of Hugin it underlies. All
four citations were checked against Crossref and arXiv. The first is PVLDB 18(3), pp. 651–665, published
November 2024 (doi:10.14778/3712221.3712232). The others match as given.

## 5. Alternatives rejected

- **A server-side playground** (Rust, Lean, Scastie). It needs hosting, a sandbox and an operator, and it
  contradicts "static". The compiler is pure, so the browser suffices.
- **TeaVM or GraalVM Web Image** (bytecode to JS or WasmGC). They would keep jgrapht and commons-text, but
  they cover less of the JDK, their Scala 3 support is weaker, and the two dependencies cost ~35 lines
  to replace (see the issue's comment).
- **CheerpJ** (a JVM in the browser). Ruled out by "fast and slim".
- **Monaco.** Several MB. Rejected in the issue.
- **Compile on every keystroke** (Gleam). It makes expensive programs freeze the result pane and churn
  workers. Instead, Run and Check are explicit buttons, and `Ctrl-Enter` runs. A debounced Check is
  possible later.
- **Bundling the explanations** (348 KB raw). The error index is one link away.
- **A playground built with a front-end framework** (React, as in lean4web and the Rust Playground). The
  page has one editor, one select and a result pane, so plain DOM code is enough.
- **mdBook or a site generator for the landing page** (4.4).

## 6. Batches

None touches the language, the reference text or the diagnostics. Sizes are changed lines including
tests.

| batch | content | conflicts with open branches | size |
|---|---|---|---|
| **W1** dependencies | BFS for `Graphs.shortestPath`; `util/Levenshtein`; `codePointAt` in `Literal.quote`; drop jgrapht and commons-text from `build.sbt` (the REPL uses the new Levenshtein too); unit tests for both | low: 5 files | S: ~80 Scala, ~60 tests |
| **W2** IO interface | `SourceFiles` (read a file, read a bundled resource) used by `Libraries`, `Explanations`, `Source`; `Cancellation` hook in `Engine`; JVM implementations are today's code | low: 5 files | S: ~120 Scala, ~40 tests |
| **W3** cross layout | `git mv` into `core/{shared,jvm}`, `cli/`, `build.sbt` with `sbt-crossproject` and `sbt-scalajs`; CI unchanged in what it runs. Purely mechanical, at a quiet moment | high: every path, so done when no branch is open or right after a merge wave | M in lines moved, ~60 lines of build |
| **W4** JS platform | `core/js` (bundled stdlib as generated source, string paths, deadline cancellation); `web` facade (run, check, phases, answers as JSON); a Node CI step that runs every single-file `tests/run` program through the bundle and diffs against `.check` (with `.flags`); bundle size printed | none | M: ~250 Scala, ~80 JS/CI |
| **W5** site and playground | `site/` (landing, playground, CSS, build script, generated highlighter); `site/example.hgn` checked like a golden; examples extracted from the reference's `hugin,run` blocks; Pages workflow building book, site and bundle into one artifact; the URL move of 4.5 with redirects and the goldens' URL update | none in code; the URL update touches 8 goldens | M: ~400 HTML/CSS/JS, ~100 Python/CI, ~30 goldens |
| **W6** Wasm measurement | build both backends; benchmark the reference examples and `bench/`; switch only if 4.1's criteria hold; record numbers in `docs/PERFORMANCE.md` | none | S |

W1 and W2 can land now, independently of each other. W3 waits for a quiet moment, or W4 and W5 use the
no-move variant of 4.3 and W3 follows later. Per the issue, W5 comes after the reference (#49) and the
README (#51) are settled.

## 7. Sources

Clones are shallow, made on 2026-10-10.

- Lean: the page lean-lang.org and its stylesheets under `-verso-data/` (read 2026-10-10); `leanprover-community/lean4web` at `9c4cd4f`:
  `README.md`, `doc/Usage.md`, `client/package.json`.
- Gleam: `gleam-lang/language-tour` at `234cb02`: `static/worker.js`, `static/compiler.js`,
  `static/index.js`, `bin/download-compiler`, `src/tour.gleam`; the release asset
  `gleam-v1.17.0-browser.tar.gz` (sizes measured).
- Scastie: `scalacenter/scastie` at `073a9c4`: `package.json`, `build.sbt`, the `sbt-runner`,
  `scala-cli-runner` and `balancer` modules.
- Rust Playground: `rust-lang/rust-playground` at `493c31b`: `README.md` ("Architecture", "Resource
  Limits"), `ui/frontend/package.json`.
- Elm: discourse.elm-lang.org, "Online REPL for teaching" (t/9523); forks of `elm/elm-lang.org`
  describing the Haskell server.
- Koka: a web search found no playground.
- CodeMirror 6: npm packages `@codemirror/view` 6.43.14, `state` 6.7.6, `language` 6.13.1, `commands`
  6.11.1, `lint` 6.9.7, `search` 6.7.2, `autocomplete` 6.20.3, `codemirror` 6.0.2; bundled with esbuild
  0.28.2.
- Scala.js 1.17.0, 1.19.0 and 1.21.0 (`sbt-scalajs`), Closure via `fullLinkJS`; Chromium 141.0.7390.37
  (Playwright), Node 22.22.
- Hugin at `bf14ffb`: `build.sbt`, `compiler/Libraries.scala`, `util/Graphs.scala`, `util/Source.scala`,
  `util/diagnostics/Explanations.scala`, `util/diagnostics/JsonDiagnostics.scala`, `runtime/Engine.scala`,
  `core/elab/Names.scala`, `core/elab/MetaTooling.scala`, `syntax/Trees.scala`, `cli/Main.scala`,
  `reference/book.toml`, `reference/README.md`, `.github/workflows/reference.yml`,
  `editors/vscode/syntaxes/hugin.tmLanguage.json`, `docs/PERFORMANCE.md` (#88), `tests/run/`,
  `bench/meta/meta_scaled.hgn`.
