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
  hugin.css        small adjustments to the default theme
  site-url.txt     the URL of the published book
```

## Building locally

Install mdBook 0.5.4 (`cargo install mdbook --version 0.5.4 --locked`, or a release binary) and Python 3,
then, from the repository root:

```
mdbook build reference        # writes reference/book/index.html
mdbook serve reference --open # rebuilds on change
```

The links are checked in CI with [lychee](https://lychee.cli.rs/) (offline: internal links and anchors):

```
lychee --offline --include-fragments --exclude-path reference/book/404.html 'reference/book/**/*.html'
```

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
