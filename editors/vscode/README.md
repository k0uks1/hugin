# Hugin for VS Code

Editor support for [Hugin](https://github.com/k0uks1/hugin) programs (`.hgn`) and facts files (`.facts`):

- syntax highlighting (TextMate grammar `syntaxes/hugin.tmLanguage.json`): nested `(* *)` comments,
  keywords, directives (`%output`), rule names (`@r`), variables, strings with `\u{...}` escapes, numbers
  and operators (`:-`, `?-`, `->`, `<:`, `|`);
- comment toggling, bracket matching and auto-closing;
- the Hugin language server (`hugin lsp`): diagnostics, hover (types, and how meta code was staged and
  which family instance a use resolved to), go to definition, find references, outline, completion,
  semantic tokens and quick fixes (the compiler's suggested edits).

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
