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
  highlight.py     mdBook preprocessor that highlights the Hugin code blocks with the compiler
  hugin.css        small adjustments to the default theme, and the colours of the highlighting
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

The links are checked in CI with [lychee](https://lychee.cli.rs/) (offline: internal links and anchors):

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

`.github/workflows/reference.yml` builds the book and checks its links on every push and pull request,
and deploys it to GitHub Pages on pushes to the default and the development branch. Deployment needs
Pages enabled with "GitHub Actions" as the source (repository settings); until then the deploy job fails
without failing the workflow. `site-url.txt` holds the published URL, the base for links to error pages
from `--explain`, the LSP's `codeDescription` and the JSON diagnostics; the path in `site-url` of
`book.toml` must match it (checked by `ReferenceExamplesSuite`).
