# Hugin for VS Code

Editor support for [Hugin](https://github.com/k0uks1/hugin) programs (`.hgn`) and facts files (`.facts`):

- syntax highlighting (TextMate grammar `syntaxes/hugin.tmLanguage.json`): nested `(* *)` comments,
  keywords (also `Type`, `data`, `where`), directives (`%output`), rule names (`@r`), variables, strings
  with `\u{...}` escapes, numbers, operators (`:-`, `?-`, `->`, `<:`, `|`), and the meta level's syntax:
  reflection quotes `'( … )`, splices and quote holes `$x`, `$..xs`, the lift `⇑` and typed holes
  `?`, `?name`;
- comment toggling, bracket matching and auto-closing;
- the Hugin language server (`hugin lsp`): diagnostics, hover (types; on the meta level the elaborated
  type and stage of the expression, the goal of a typed hole, a directive's footprint, the two stages of
  a shared type; how meta code was staged and which family instance a use resolved to), go to
  definition, find references (also of pattern variables, lambda parameters and `where` bindings),
  outline, completion (type-directed and quote-aware on the meta level), semantic tokens (meta and object
  names tell apart by the modifiers `meta` and `object`), inlay hints (inferred quotes, splices and
  implicit arguments), quick fixes (the compiler's suggested edits, the missing clauses of a function),
  splitting a pattern variable by its constructors, and the expansion of directives and functor
  applications (the command **Hugin: Show Expansion** and the code lenses above them).

## Setup

The extension starts `hugin lsp`. Build the launcher in the Hugin checkout (`sbt stage`) and either put
`bin/hugin` on the `PATH` or set `hugin.server.path` to it. Highlighting works without the server.

```
npm install
code --extensionDevelopmentPath=$PWD <folder with .hgn files>   # run from source
npm run package                                                 # build hugin-<version>.vsix
code --install-extension hugin-0.1.0.vsix
```

CI builds the `.vsix` on every push: download the artifact `hugin-vscode` of a workflow run.

## Settings

- `hugin.server.path`: the `hugin` executable (default `hugin`).
- `hugin.trace.server`: `off`, `messages` or `verbose`; traces the protocol in the `Hugin` output channel.
- `hugin.inlayHints.staging`, `hugin.inlayHints.implicits` (both on by default) and
  `hugin.inlayHints.levels` (off): which inlay hints are shown (the quotes `⟨ ⟩`, splices `$` and lifts
  `⇑` stage inference inserted; inferred implicit arguments; universe levels).

## Commands

- **Hugin: Show Expansion** (`hugin.showExpansion`, also in the editor's context menu): opens the staged
  object code of the directive application, functor application or item at the cursor beside the editor.
