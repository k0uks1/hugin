# The Hugin language reference

The normative definition of Hugin (issue #49), built with [mdBook](https://rust-lang.github.io/mdBook/)
into a static site and published on GitHub Pages at the URL in `site-url.txt`. The design notes under
`docs/` are historical; this book is the specification.

```
reference/
  book.toml        mdBook configuration
  src/SUMMARY.md   table of contents: every page must be listed here
  src/**/*.md      the chapters
  src/errors/index.md  the error index (its code pages are generated, see below)
  error-index.py   mdBook preprocessor that generates the error index
  highlight.py     mdBook preprocessor that highlights the Hugin code blocks with the compiler, with
                   hovers and definition links
  hugin-info.js    the popups of the hovers (mdBook `additional-js`)
  hugin-info-smoke.cjs  the Playwright smoke test of the hovers (mouse, keyboard, touch)
  hugin.css        small adjustments to the default theme, the colours of the highlighting and the popups
  site-url.txt     the URL of the published book
```

## Building locally

Install mdBook 0.5.4 (`cargo install mdbook --version 0.5.4 --locked`, or a release binary) and Python 3,
then, from the repository root:

```
sbt stage                     # the compiler, which highlights the code blocks (once, and after changes)
mdbook build reference        # writes reference/book/index.html
mdbook serve reference --open # rebuilds on change
```

Without a staged compiler (`target/universal/stage/bin/hugin`) the build stops with a message saying so.
`HUGIN=<launcher>` names another one, relative to the repository root unless absolute: with
`HUGIN=bin/hugin mdbook build reference`, `bin/hugin` stages the compiler on first use. Re-stage after
changing the compiler, or the book shows the old highlighting.

The links are checked in CI with [lychee](https://lychee.cli.rs/) (offline: internal links and anchors),
as part of the website built around the book (see CONTRIBUTING.md, "The website"):

```
lychee --offline --include-fragments --exclude-path reference/book/404.html 'reference/book/**/*.html'
```

## Style

`STYLE.md` is the style guide of the book and of `docs/errors`. `scripts/check-style.sh` checks its word
list in CI (job "Formatting"); run it before a commit.

## Code blocks

Every fenced block whose info string starts with `hugin` is checked by `sbt test`
(`src/test/scala/hugin/reference/ReferenceExamplesSuite.scala`). Attributes follow rustdoc and mdBook,
separated by commas:

| info string | checked by the test |
|---|---|
| ` ```hugin ` | compiles without errors (with the prelude) |
| ` ```hugin,compile_fail,E0603 ` | its first error is `E0603` |
| ` ```hugin,run ` | compiles, runs, and prints exactly the ` ```output ` block that follows |
| ` ```hugin,ignore ` | not checked (fragments, grammar schemata) |

A ` ```facts ` block right after a `hugin` block is loaded as its input facts; for `run` it comes before
the ` ```output ` block. Unknown attributes fail the test. Blocks in other languages (`text`, `output`,
...) are not checked. Every example is a complete program: there are no hidden lines.

## Highlighting

The Hugin code blocks are highlighted by the compiler, with the semantic tokens of the language server:
a name is coloured by what it is (a type, a relation, a constructor, a meta function, a variable, ...),
not by how it looks. `highlight.py`, an mdBook preprocessor that runs after `error-index.py` (so the
error pages are included), collects every block whose info string starts with `hugin` and pipes them, as
one JSON array, to `hugin highlight`, an internal command of the compiler (one JVM for the whole book;
`src/main/scala/hugin/cli/Highlight.scala`). For each block it returns the text cut into runs with
classes:

- the semantic tokens exactly as `hugin lsp` sends them (`hugin.lsp.Tokens`): the token type
  (`type`, `struct`, `function` for relations, `enumMember` for constructors, `method` for meta functions,
  `class` for meta families, `namespace`, `macro` for formula functions, `parameter`, `variable`,
  `decorator` for directives, `keyword` and `operator` for quotes and splices, `label` for holes) and its
  modifiers (`declaration`, `meta`, `object`, `defaultLibrary`);
- for the text these do not cover, lexical classes from the compiler's lexer: `comment`, `string`,
  `number`, `keyword`, `operator` (`:-`, `?-`, `->`, `<:`, `::`), `decorator`, `variable`, `type` (the
  universe `Type`) and `label` (rule names).

Each block is compiled as the reference tests compile it: as a program of its own, with the prelude
(without it for the `elaborate` blocks of `docs/errors`); `std/` imports work as in a test. Blocks that
do not compile (`compile_fail`, `ignore`, fragments) keep the lexical classes and whatever the compiler's
recovery resolved. The preprocessor replaces the fence with `<pre><code class="hugin hljs nohighlight">`
and a `<span class="hg-<class> ...">` per run; mdBook passes the HTML through, highlight.js skips the block
(`nohighlight`; a `language-hugin` class would make it warn about an unknown language), and the
copy button copies the text. `hugin.css` colours the classes for each mdBook theme from the palette of
its highlight.js theme; declarations are bold, meta parameters italic.

## Hovers and definitions

The names in the code blocks show what the language server's hover shows, and link to their declarations
(issue #132, `docs/design/web-ide.md`, section 7). `highlight.py` runs `hugin highlight --info`, which
also returns each block's annotation table (`hugin.ide.Annotations`): the names of the block with their
hover texts, their declarations (an offset in the block, or a module and a name of the bundled standard
library) and their occurrence groups; a run that is exactly a name carries the name's index (the format
is in `CONTRIBUTING.md`, "Editor support"). The landing page's build uses `hugin highlight` without
`--info`, and has no hovers. For each page, the preprocessor writes:

- each name as `<span data-i="n">`, or, if it has a declaration, as `<a data-i="n" href="…"
  tabindex="-1">`: a use links to its declaration in the same block (`id="hg<block>-<name>"`; each block
  is a program of its own), a name of the bundled library to its module's page (`std/graph.html`,
  `prelude.html`) at the row of the page's declaration table that lists it first (`#hg-<name>`, an anchor
  the preprocessor adds to the first cell). The links work without JavaScript;
- the page's hover texts, deduplicated over its blocks, once, as JSON after the text:
  `<script type="application/json" id="hg-hovers">[[signature, note, …], …]</script>`; `data-i`
  indexes it, and a block with names gets `data-hg`, `tabindex="0"` and an `aria-label`.

`hugin-info.js` shows the hover text of a name in one popup (`role="tooltip"`): after 300 ms under the
mouse; on the keyboard, a block is one tab stop, ArrowRight and ArrowLeft (Home, End) move between its
names and show their popup, Enter follows the link, Escape returns to the block and Tab leaves it; on a
touch screen, the first tap on a name shows its popup, with a "Definition" link, and a second tap or a tap
outside closes it. The occurrences of the name in its block are marked. The texts are read with
`JSON.parse` and inserted as text.

The budget: the hovers, links and anchors may add at most 8 KB gzip to a page. `highlight.py` prints the
largest and the median page's figure on every build and fails the build above the budget
(`HUGIN_INFO_BUDGET=<bytes>` sets another, to try the check). `hugin-info-smoke.cjs` checks the mouse,
keyboard and touch behaviour in Chromium (CI runs it after building the book):

```
npm install --no-save --prefix /tmp/pw playwright@1.56.1 && /tmp/pw/node_modules/.bin/playwright install chromium
NODE_PATH=/tmp/pw/node_modules node reference/hugin-info-smoke.cjs reference/book [<screenshot dir>]
```

The Markdown sources keep their fences and attributes: the tests read the sources, not the HTML.
Editors highlight with the TextMate grammar of the VS Code extension
(`editors/vscode/syntaxes/hugin.tmLanguage.json`) under the language server's semantic tokens.

## The error index

The appendix "Error index" has one page per diagnostic code, at `errors/<code>.html` (for example
`errors/E0603.html`), so `<site-url>errors/<code>.html` is the stable URL of a code. The pages are not
checked in: `error-index.py` is an mdBook preprocessor (configured in `book.toml`) that reads
`docs/errors/<code>.md` on every build, adds a page for each under `src/errors/index.md`, appends a table
of all codes to that chapter and links mentions of other codes. The index is therefore always up to date;
`docs/errors` stays the single source, also of `hugin explain`, and its examples are checked by
`ExplanationsSuite`.

Links from the chapters to a code use a relative path, e.g. `[E0603](../errors/E0603.md)` from a page
under `src/object/`.

## Publishing

`.github/workflows/reference.yml` (workflow "Site") builds the book into the website (issue #58: the
landing page at `/hugin/`, the book at `/hugin/reference/`, the playground at `/hugin/play/`; built by
`site/build.mjs`) and checks its links on every push and pull request, and deploys the site to GitHub
Pages on pushes to the default and the development branch. The book's pages at their URLs before the
move (`/hugin/<page>.html`, among them `/hugin/errors/<code>.html`) are redirect pages to their new URLs,
so links to them keep working. Deployment needs
Pages enabled with "GitHub Actions" as the source (repository settings); until then the deploy job fails
without failing the workflow. `site-url.txt` holds the published URL, the base for links to error pages
from `--explain`, the LSP's `codeDescription` and the JSON diagnostics; the path in `site-url` of
`book.toml` must match it (checked by `ReferenceExamplesSuite`).
