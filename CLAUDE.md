# Working on Hugin

Read `CONTRIBUTING.md` before changing anything. Two rules matter most:

- **The language reference is the definition of the language.** Any change to the syntax, the static
  rules, the semantics, the diagnostics or the bundled library updates the reference (`reference/src/`,
  and `docs/errors/` for diagnostics) in the same commit series and the same pull request. Never defer
  the reference to a later batch or a "docs" pull request. See CONTRIBUTING.md, "Changing the language";
  CI enforces it with `scripts/check-reference-impact.sh`.
- Do not run the full test suite locally; run the suites you touched with `testOnly`. CI runs everything.
