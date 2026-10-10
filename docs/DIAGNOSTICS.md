# Diagnostics: survey and design

Status: **implemented** (steps M1–M5 and the retirements of M6, see [§3.12](#312-migration-plan); the
wording review of M6 remains). Written as the proposal for [issue #41](https://github.com/k0uks1/hugin/issues/41)
and kept as the record of the design; Part 2 describes the code before M1. The explanations are published as
the [error index](https://k0uks1.github.io/hugin/reference/errors/index.html) of the language reference. It interacts with the redesign ([`docs/REDESIGN.md`](REDESIGN.md), issue #40): the new
meta elaborator (Phase B) and the size-change termination checker (Phase A1) will add many diagnostics,
so the typed core described here should land **before Phase B3 and Phase C**.

The document has three parts:

1. **[Survey](#part-1--survey)**: how rustc, Scala 3 (dotty), Elm, Roc, GHC, TypeScript, Swift, Lean 4
   and Gleam declare, word, number, test and ship their diagnostics, and what their maintainers say works.
2. **[Hugin today](#part-2--hugin-today)**: what `util/Diagnostics.scala` and `util/ErrorCodes.scala`
   already do well, with numbers, and where they break down.
3. **[Design](#part-3--design-for-hugin)**: Scala 3 types, wording, explanations, style guide, JSON, LSP,
   testing, and a migration plan in steps with acceptance criteria, ending with two current diagnostics
   rewritten in the new style.

**Summary.** Every system that has scaled its diagnostics converged on the same core: *a diagnostic is a
typed value* (a struct, a constructor of a sum type, or a class) whose fields are the data it needs, and
*rendering is derived from that value*. Codes are registered in one place, are append-only and are never
reused. Long explanations live next to the registry as Markdown with examples that a test compiles.
Suggestions carry an applicability, so tools know which ones they may apply on their own. Where systems
differ is *where the English goes*. rustc moved its wording into Fluent files in 2022 and, by an accepted
proposal in January 2026, is moving it back inline into the diagnostic structs. That is strong evidence
for keeping Hugin's wording in Scala, next to the data. For Hugin, the proposal is:

* an `enum Code` registry;
* one `enum` of problems per phase, where each case holds typed fields and defines its own message,
  labels, notes, helps and suggestions;
* a structured message type `Msg` built by a typed interpolator;
* Markdown explanations with compiled examples;
* JSON output and LSP code descriptions and code actions, all derived from the same value;
* a coverage test that ties every code to a negative test and an explanation.

Migration starts with the phases the redesign is rewriting anyway, and leaves the old meta typer, which
emits 65% of today's diagnostics and is deleted in B3, on a counted legacy path.

---

## Part 1 — Survey

For each system: how diagnostics are **declared**, where the **wording** lives, how **codes** are assigned,
how **arguments** are typed, how **suggestions** are represented, how they are **tested**, how **tools**
consume them, and what maintainers and users say about it.

### 1.1 rustc

**Declaration.** Since 2022 most rustc diagnostics are structs that derive `Diagnostic` (or
`Subdiagnostic` for reusable parts such as a note or a suggestion, and `LintDiagnostic` for lints),
defined in each crate's `errors.rs` or `diagnostics.rs`. Attributes mark the parts:
`#[diag(...)]` for the headline and the code, `#[primary_span]`, `#[label]`, `#[note]`, `#[help]`,
`#[suggestion(code = "...", applicability = "...")]`, `#[multipart_suggestion]` with
`#[suggestion_part]`, and `#[subdiagnostic]` for a field holding a subdiagnostic
([dev guide: diagnostic structs](https://rustc-dev-guide.rust-lang.org/diagnostics/diagnostic-structs.html)).
Current `master` of `rustc_parse/src/diagnostics.rs`
([source](https://github.com/rust-lang/rust/blob/master/compiler/rustc_parse/src/diagnostics.rs)):

```rust
#[derive(Diagnostic)]
#[diag("expected a path on the left-hand side of `+`", code = E0178)]
pub(crate) struct BadTypePlus {
    #[primary_span]
    pub span: Span,
    #[subdiagnostic]
    pub sub: BadTypePlusSub,
}

#[derive(Subdiagnostic)]
#[multipart_suggestion("try adding parentheses", applicability = "machine-applicable")]
pub(crate) struct AddParen {
    #[suggestion_part(code = "(")]
    pub lo: Span,
    #[suggestion_part(code = ")")]
    pub hi: Span,
}
```

The call site is `dcx.emit_err(BadTypePlus { span, sub })`. Older code builds diagnostics imperatively
with `struct_span_code_err!(...)` followed by `.span_label(...)`, `.note(...)` and `.emit()`, and that
style still exists. A diagnostic that is not emitted, or not explicitly cancelled, panics on drop, which
catches lost errors.

**Wording: from Fluent and back.** In 2022 the translation effort moved messages into per-crate Fluent
files (`messages.ftl`, with ids like `parse_bad_type_plus` and arguments `{$name}`), and the structs
referred to them by slug. The dev guide has said for a while that the infrastructure "causes some
friction for compiler contributors" and that contributors are "not mandat[ed]" to use it
([translation chapter](https://rustc-dev-guide.rust-lang.org/diagnostics/translation.html)). In January
2026 MCP [compiler-team#959 "Remove the fluent files"](https://github.com/rust-lang/compiler-team/issues/959)
was **accepted**. Its reasons: the files "being decoupled from the rest of the diagnostics reduces the
ergonomics of working on the compiler"; interpolation may make real translation impractical anyway; and
no translation effort is under way. Messages move back inline (`#[diag("...")]`, as above), and
struct diagnostics "are still the preferred and recommended way". On current `master`, crates such as
`rustc_parse` have no `messages.ftl` any more. Fluent remains only as an internal formatting engine.

**Arguments.** Fields are converted with the `IntoDiagArg` trait to `DiagArgValue` (a string or a
number) and interpolated by name. Types, paths and identifiers implement `IntoDiagArg`, so the struct
holds rich values and formatting is centralised.

**Codes.** `rustc_error_codes` is the single registry: an `error_codes!` macro lists every number, and
each code has a long explanation `error_codes/EXXXX.md`. Codes are never removed. A retired code keeps its
file with "#### Note: this error code is no longer emitted by the compiler" and its examples are marked
`ignore` ([`lib.rs`](https://github.com/rust-lang/rust/blob/master/compiler/rustc_error_codes/src/lib.rs)).
Explanations follow [RFC 1567](https://rust-lang.github.io/rfcs/1567-long-error-codes-explanation-normalization.html):
a one-sentence summary, an "Erroneous code example" in a ` ```compile_fail,E0384 ` block, an explanation
of *why*, and fixed examples
([E0384.md](https://github.com/rust-lang/rust/blob/master/compiler/rustc_error_codes/src/error_codes/E0384.md)).
The examples are doctests: a `compile_fail,EXXXX` block must fail *with that code*. tidy also checks that
every code has an explanation and a UI test. `rustc --explain E0384` prints the file, and the
[error index](https://doc.rust-lang.org/error_codes/error-index.html) renders all of them. Not every error
gets a code: the guide says to assign one when the long explanation adds real value
([dev guide: diagnostics](https://rustc-dev-guide.rust-lang.org/diagnostics.html),
[error codes](https://rustc-dev-guide.rust-lang.org/diagnostics/error-codes.html)).

**Suggestions and applicability.** Every suggestion has an `Applicability`
([docs](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_errors/enum.Applicability.html)):

| variant | meaning |
|---|---|
| `MachineApplicable` | "definitely what the user intended, or maintains the exact meaning"; tools may apply it automatically |
| `MaybeIncorrect` | may be what the user meant; the result should still compile |
| `HasPlaceholders` | contains placeholders such as `(...)`; cannot be applied without editing |
| `Unspecified` | unknown |

`cargo fix` (rustfix) applies only `MachineApplicable` suggestions, and the guide asks authors to be
conservative.

**Lints.** Warnings that users may want to silence are lints, not hard-coded warnings. A lint is declared
with `declare_lint!` (name, default level `Allow`/`Warn`/`Deny`/`Forbid`, one-line description), and its
doc comment includes an `### Example` and an `### Explanation`. The `{{produces}}` marker is replaced by the
real compiler output when the lint docs are generated, so the examples are checked
([`rustc_lint_defs/src/builtin.rs`](https://github.com/rust-lang/rust/blob/master/compiler/rustc_lint_defs/src/builtin.rs)).
Lints are grouped (`unused`, `future_incompatible`), and levels are set with `#[allow]`, `#[expect]` or
`-W`/`-A`/`-D`. The guide says "hard-coded warnings should be avoided for normal code", and gives naming
rules (a lint name should read well as "allow *name*").

**Testing.** UI tests (`tests/ui/**/*.rs`) store the rendered stderr in `.stderr` files, updated with
`--bless`. In addition, the source is annotated inline with `//~ ERROR`, `//~^ ERROR` and similar, and the
annotations must account for **every** error and warning. That gives a check on code and line which is
independent of wording. `//@ run-rustfix` applies the machine-applicable suggestions, compares the result
with a `.fixed` file and checks that it compiles
([dev guide: UI tests](https://rustc-dev-guide.rust-lang.org/tests/ui.html)).

**Tools.** `--error-format=json` emits one JSON object per diagnostic: `message`, `code
{code, explanation}`, `level`, `spans[]`, `children[]` and `rendered`. Each span has `is_primary`,
`label`, `suggested_replacement`, `suggestion_applicability` and a macro `expansion` chain
([rustc book: JSON](https://doc.rust-lang.org/rustc/json.html)). cargo, rustfix and rust-analyzer's
"flycheck" all consume it, and `rendered` lets a tool show exactly what the terminal would.

**What works, what doesn't.** Struct diagnostics are considered a success: the data is typed, they are
greppable, and subdiagnostics are reusable. Externalised wording was not a success, and is being undone.
Applicability plus JSON is what makes `cargo fix` and editor quick-fixes possible. The style guide is
widely copied.

### 1.2 Scala 3 (dotty)

**Declaration.** `dotty.tools.dotc.reporting`. One class per message in
[`messages.scala`](https://github.com/scala/scala3/blob/main/compiler/src/dotty/tools/dotc/reporting/messages.scala)
(about 4,000 lines). Each class extends a kind-specific base (`SyntaxMsg`, `TypeMsg`, `NotFoundMsg`, …)
that fixes a `MessageKind` (Syntax, Type Mismatch, Not Found, Cyclic, Unused Symbol, Staging, …), and
implements `msg` (the headline and body) and `explain` (the long explanation)
([`Message.scala`](https://github.com/scala/scala3/blob/main/compiler/src/dotty/tools/dotc/reporting/Message.scala)):

```scala
class MissingEmptyArgumentList(method: String, tree: tpd.Tree)(using Context)
  extends SyntaxMsg(MissingEmptyArgumentListID) {
  def msg(using Context) = i"$method must be called with ${hl("()")} argument"
  def explain(using Context) = i"""Previously an empty argument list () was implicitly inserted ..."""
  override def actions(using Context) =
    List(CodeAction(title = "Insert ()", description = None,
      patches = List(ActionPatch(SourcePosition(tree.source, tree.span.endPos), "()"))))
}
```

Messages are computed lazily, so a suppressed message costs nothing. A message that mentions an error
type is "non-sensical" and is dropped as a follow-up error.

**Codes.** [`ErrorMessageID`](https://github.com/scala/scala3/blob/main/compiler/src/dotty/tools/dotc/reporting/ErrorMessageID.scala)
is a Java-style enum whose ordinal is the number shown (`E007`). The rules, in a banner at the top of the
file, are: "Only add new IDs at end of the enumeration list and never remove IDs". Retired ids stay, as
`extends ErrorMessageID(isActive = false)`. `NoExplanationID` (-1) is the escape hatch for plain-string
errors: `report.error(em"...")` wraps the string in `NoExplanation`. The escape hatch is used heavily. In
`typer/Typer.scala`, about 30 of the 71 `report.error`/`report.warning` calls pass a string literal rather than
a message class.

**Explanations.** `-explain` appends `explain` to the rendered message. There are also
per-code pages under
[`docs/_docs/reference/error-codes/`](https://github.com/scala/scala3/tree/main/docs/_docs/reference/error-codes)
([E007](https://github.com/scala/scala3/blob/main/docs/_docs/reference/error-codes/E007.md)). They have
an example tagged `sc:fail`, the actual output, and solutions tagged `sc:compile`; the doc tool's snippet
checker compiles the examples.

**Arguments.** The `i"..."`/`em"..."` interpolators take `Shown*`. `Shown` is an opaque type, and
`given [A: Show]: Conversion[A, Shown]` lets any value with a `Show` instance (types, symbols, trees) be
interpolated with consistent highlighting and automatic disambiguation (`where: T is a type in class C`)
([`Formatting.scala`](https://github.com/scala/scala3/blob/main/compiler/src/dotty/tools/dotc/printing/Formatting.scala)).
This is the Scala 3 precedent for a typed message interpolator.

**Suggestions and tools.** `Message.actions` returns
[`CodeAction(title, description, patches)`](https://github.com/scala/scala3/blob/main/compiler/src/dotty/tools/dotc/reporting/CodeAction.scala).
These travel through the compiler interface, Zinc and BSP (the `data` field of a diagnostic) to Metals,
which shows them as quick fixes. Getting there took a multi-project effort
([roadmap for actionable diagnostics](https://contributors.scala-lang.org/t/roadmap-for-actionable-diagnostics/6172),
[Metals 1.0](https://scalameta.org/metals/blog/2023/10/17/silver)). A `Diagnostic` has one position plus
`RelatedInformation`. There are no labelled secondary spans as in rustc, and no applicability: an action is
an action.

**Testing.** `tests/neg/*.scala` with `// error` comments on the offending lines (checked by line), and
`.check` files with the rendered output for some tests.

**Assessment.** One class per message gives an inventory and a place for `explain`. The weak points are
the string escape hatch, which is used so widely that the inventory is incomplete; ordinal-based numbering,
which is fragile; and the lack of secondary labels.

### 1.3 Elm

**Declaration.** Each phase has its own error *data type*, and a top-level sum type collects them
([`Reporting/Error.hs`](https://github.com/elm/compiler/blob/master/compiler/src/Reporting/Error.hs)):
`data Error = BadSyntax Syntax.Error | BadImports ... | BadNames ... | BadTypes Localizer ... |
BadMains ... | BadPatterns ... | BadDocs ...`. Each module `Reporting/Error/*.hs` has a `toReport`
function that turns its errors into a
[`Report`](https://github.com/elm/compiler/blob/master/compiler/src/Reporting/Report.hs) — a title,
a region, a list of suggestions and a `Doc`.

**Wording.** Wording lives in `toReport`, as pretty-printer documents
([`Reporting/Doc.hs`](https://github.com/elm/compiler/blob/master/compiler/src/Reporting/Doc.hs):
`reflow`, `stack`, `toSimpleHint`, `toFancyHint`, `link`, `ordinal`, `cycle`). The style is that of a
helpful colleague: full sentences, first person ("I am having trouble with ..."), a code snippet with the
region underlined, and "Hint:" and "Note:" paragraphs
([Compiler Errors for Humans](https://elm-lang.org/news/compiler-errors-for-humans),
[Compilers as Assistants](https://elm-lang.org/news/compilers-as-assistants)).

**The key idea is data about *why*.** The type checker records not only the expected type but where the
expectation came from
([`Reporting/Error/Type.hs`](https://github.com/elm/compiler/blob/master/compiler/src/Reporting/Error/Type.hs)):

```haskell
data Error = BadExpr A.Region Category T.Type (Expected T.Type) | BadPattern ... | InfiniteType ...
data Expected tipe
  = NoExpectation tipe
  | FromContext A.Region Context tipe            -- e.g. CallArg name index, IfBranch i, OpLeft op
  | FromAnnotation N.Name Int SubContext tipe    -- the 2nd branch of this `case` vs the annotation
```

`toReport` then says "The 2nd argument to `foo` is …, but the type annotation on `foo` says …". Good
messages come from carrying *provenance* in the error value, not from clever wording at the call site.

**Codes, explanations, fixes.** Elm has no numeric codes. The title (`TYPE MISMATCH`, `NAMING ERROR`) acts
as a category, and hints link to longer documents on the web. There are no machine-applicable
suggestions. `--report=json` emits the `Doc` as styled chunks (`Doc.encode`).

**Assessment.** Elm's messages are the reference for tone and helpfulness. The lack of codes and fixes
hurts tooling.

### 1.4 Roc

Roc follows Elm; its compiler has been rewritten from Rust to Zig. Each phase
has a tagged union of problems with typed payloads. For example, `canonicalize/Diagnostic.zig` declares
`pub const Diagnostic = union(enum) { not_implemented: struct { feature, region }, ... }`
([source](https://github.com/roc-lang/roc/blob/main/src/canonicalize/Diagnostic.zig)), and the checker has
`check/problem.zig`. Problems are turned into a
[`Report`](https://github.com/roc-lang/roc/blob/main/src/reporting/report.zig): a `title`, a one-sentence
`headline`, a `severity` (`warning`, `runtime_error`, `fatal`) and a `Document` of *semantic* elements
(text, `inline_code`, `type_variable`, `symbol`, `suggestion`, code regions). The document is rendered to
terminal, Markdown, HTML and LSP by separate renderers
([`reporting/mod.zig`](https://github.com/roc-lang/roc/blob/main/src/reporting/mod.zig)). Snapshot tests
can use a canonical, presentation-independent S-expression form of the report (`report_sexpr.zig`), so
tests compare structure, not ANSI text. The severity `runtime_error` reflects Roc's "always run" policy:
code with an error compiles to a crash at that point.

**Takeaways.** A semantic document model, rather than a string, lets one report feed several renderers,
and snapshots can be taken of structure.

### 1.5 GHC (9.4 and later)

**Declaration.** The "errors as structured values" project
([GHC wiki](https://gitlab.haskell.org/ghc/ghc/-/wikis/Errors-as-(structured)-values)) replaced
`SDoc`-valued errors with one large sum type per phase: `PsMessage` (parser), `TcRnMessage`
(renamer and type checker), `DsMessage` (desugarer), `DriverMessage`, all collected in `GhcMessage`. Each
type is an instance of the
[`Diagnostic` class](https://gitlab.haskell.org/ghc/ghc/-/blob/master/compiler/GHC/Types/Error.hs):
`diagnosticMessage` (a structured document), `diagnosticReason` (an error, or the warning flag that
enabled it), `diagnosticHints :: a -> [GhcHint]` and `diagnosticCode`. Hints are a typed sum of their own
(`GhcHint`: suggest an extension, suggest an import, …), so IDEs can act on them.

**Codes.** Codes look like `[GHC-39999]`. They are assigned in one module,
[`GHC.Types.Error.Codes`](https://gitlab.haskell.org/ghc/ghc/-/blob/master/compiler/GHC/Types/Error/Codes.hs),
as equations of an **injective type family** from constructor names:
`GhcDiagnosticCode "TcRnUnknownMessage" = ...`. Injectivity makes a duplicate number a *compile error*.
The code of a value is derived generically from its constructor (`constructorCode` via `GHC.Generics`), so
a call site cannot pick the wrong code. A constructor that wraps a finer reason type can recurse into it
(`ConRecursInto`), which gives fine codes without flattening the types. Numbers are drawn **at random**
(the note links random.org) so that they carry no ordering or grouping that could become wrong. They are
never deleted: old ones are marked `Outdated`, and a testsuite check ("codes") verifies that every
non-outdated code is exercised by some test.

**Explanations and tools.** The [Haskell Error Index](https://errors.haskell.org/) is community-maintained
by the Haskell Foundation, outside the compiler, with examples per code (and codes from Cabal, Stack and
GHCup). `-fdiagnostics-as-json` (GHC 9.10) emits diagnostics against a versioned JSON schema; schema 1.2 in
GHC 9.14 added `rendered`
([schema](https://downloads.haskell.org/ghc/9.14.1/docs/users_guide/_downloads/aade9215bf1b87075759c4d918fa42d3/diagnostics-as-json-schema-1_1.json)).
HLS consumes the structured values directly, because it links against GHC.

**Assessment.** The type-level registry and the coverage test are excellent ideas. The migration took
several releases, with an `UnknownDiagnostic` escape hatch, and the escape hatch and coverage gaps are
still being reduced. Random numbers prevent bikeshedding but give no phase hint to users.

### 1.6 TypeScript

**Declaration and wording.** A single JSON file,
[`src/compiler/diagnosticMessages.json`](https://github.com/microsoft/TypeScript/blob/v5.8.3/src/compiler/diagnosticMessages.json),
maps the **English text** to `{category, code}`: about 2,100 entries in 5.8, of which 1,336 are errors,
746 are "Message" (used, among other things, for code-fix titles) and 21 are suggestions. Flags such as
`reportsUnnecessary` and `reportsDeprecated` become LSP tags. A generator turns the file into typed
constants (`Diagnostics.Cannot_find_name_0`), and the Go port generates the same constants
([`typescript-go/internal/diagnostics/generate.go`](https://github.com/microsoft/typescript-go/blob/main/internal/diagnostics/generate.go)).
Arguments are positional (`{0}`) and untyped, and the localisation team translates the file.

**Codes.** Codes are numeric and grouped by thousands (1xxx syntax, 2xxx semantic, …). Because the key is
the text, **every variant of a sentence is a new code**: "Cannot find name '{0}'." (2304), "… Did you mean
'{1}'?" (2552), "… Did you mean to write this in an async function?" (2311), and so on.

**Suggestions.** Fixes are *decoupled* from diagnostics. A code fix registers the error codes it handles
and recomputes the edit from the program at the diagnostic's position
([`codefixes/fixSpelling.ts`](https://github.com/microsoft/TypeScript/blob/v5.8.3/src/services/codefixes/fixSpelling.ts)
handles about a dozen codes). This allows "fix all in file" (`fixId`), but the information has to be
rediscovered.

**Testing.** Baselines (`tests/baselines/reference/*.errors.txt`) are golden files of rendered errors;
fourslash tests cover code fixes.

**Assessment.** A central text file makes localisation and wording review easy. It also produces code
explosion, untyped arguments and no inventory of *concepts*. Decoupled fixes are flexible but duplicate
analysis.

### 1.7 Swift

**Declaration.** X-macro `.def` files per area (`DiagnosticsParse.def`, `DiagnosticsSema.def`, …; Sema
alone has about 9,800 lines and 1,870 errors) declare `ERROR(id, options, "format", (argument types))`,
`WARNING`, `NOTE` and `REMARK`
([`DiagnosticsSema.def`](https://github.com/swiftlang/swift/blob/main/include/swift/AST/DiagnosticsSema.def)):

```cpp
ERROR(cannot_find_in_scope,none,
      "cannot %select{find|find operator}1 %0 in scope", (DeclNameRef, bool))
```

The argument **types** are part of the declaration, and `diagnose(loc, diag::cannot_find_in_scope, name,
isOperator)` is type-checked against them. The format language has `%select`, `%s` (plural) and typed
formatting of declarations and types. Fix-its are attached at the call site (`.fixItReplace`,
`.fixItInsert`).

**Codes and explanations.** There are no public numeric codes. Since 2024,
[`DiagnosticGroups.def`](https://github.com/swiftlang/swift/blob/main/include/swift/AST/DiagnosticGroups.def)
declares named groups (`GROUP(ActorIsolatedCall, none, "actor-isolated-call")`). `GROUPED_ERROR` and
`GROUPED_WARNING` attach a diagnostic to a group. The group name is shown in the message, links to
`userdocs/diagnostics/<file>.md`, and is used by `-Werror <group>` and `-Wwarning <group>`. The file says
that "new warnings and errors should be introduced along with groups". These group documents absorbed the
older "educational notes".

**swift-syntax** (the new parser and macros) uses a protocol instead
([`SwiftDiagnostics`](https://github.com/swiftlang/swift-syntax/tree/main/Sources/SwiftDiagnostics)):
`protocol DiagnosticMessage { var message: String; var diagnosticID: MessageID; var severity: ... }` with
`MessageID(domain, id)`, and `Diagnostic(node, message, highlights, notes, fixIts)`, where a `FixIt` has a
`FixItMessage` and a list of changes. Parser errors are an enum conforming to the protocol.

**Testing.** `-verify` mode: `// expected-error {{cannot find 'x' in scope}}` comments, with optional
fix-it checks, matched against the actual diagnostics.

**Assessment.** Typed argument lists in a central table catch argument mismatches at compile time. The
`%select` language is powerful but cryptic. Named groups that double as documentation keys and as warning
controls are a good idea.

### 1.8 Lean 4 and Gleam (briefly)

* **Lean 4.** `MessageData` is a structured, lazily formatted document (expressions in it stay
  interactive in the infoview). Since 4.22, errors can be **named** (`lean.unknownIdentifier`), thrown with
  `throwNamedError`, and registered with `register_error_explanation`. The metadata includes a summary,
  `sinceVersion` and `removedVersion`. The explanation is rendered in the reference manual and linked from
  the message ([error explanations](https://lean-lang.org/doc/reference/4.22.0-rc4/Error-Explanations/),
  [API](https://lean-lang.org/doc/api/Lean/ErrorExplanation.html)). Named codes are readable, and naming
  can be adopted gradually.
* **Gleam** (Rust) has one `Error` enum with typed variants and a large `to_diagnostics` match producing
  `Diagnostic { title, text, level, location: { label, extra_labels }, hint }`
  ([`diagnostic.rs`](https://github.com/gleam-lang/gleam/blob/main/compiler-core/src/diagnostic.rs),
  [`error.rs`](https://github.com/gleam-lang/gleam/blob/main/compiler-core/src/error.rs)). It uses Elm-like
  prose, no codes and `insta` snapshot tests, and the language server computes code actions separately.

### 1.9 Comparison

| | declaration | wording lives in | codes | typed args | fixes | explanation tested | machine output |
|---|---|---|---|---|---|---|---|
| rustc | `#[derive(Diagnostic)]` structs | inline in the struct attribute (Fluent being removed) | `E0123`, central macro, append-only | yes (`IntoDiagArg`) | spans + `Applicability` | yes (`compile_fail,E…` doctests) | JSON, versioned by convention |
| dotty | class per message | `msg`/`explain` methods | `E007` = enum ordinal, append-only | yes (`Shown`/`Show`) | `CodeAction` (no applicability) | yes (snippet checker) | via BSP `data` |
| Elm | sum type per phase + `toReport` | `Doc` in `toReport` | none (titles) | yes (ADT fields) | none | – | JSON of `Doc` |
| Roc | tagged union per phase | report builders, semantic `Document` | none | yes | limited | – | LSP/HTML/Markdown renderers |
| GHC | sum type per phase + `Diagnostic` class | `diagnosticMessage` | `GHC-12345`, injective type family, random, append-only | yes | typed `GhcHint` | external index | JSON (versioned schema) |
| TypeScript | JSON text → generated constants | the JSON file | numeric, keyed by text | no (`{0}`) | separate code-fix registry by code | – | LSP (tsserver) |
| Swift | `.def` X-macros / swift-syntax protocol | `.def` format strings | named groups | yes (declared tuple) | fix-its at call site | – | serialized diagnostics |
| Lean 4 | `throwError`/`throwNamedError` | `m!"..."` at call site | named (`lean.x`) | `MessageData` | code actions via widgets | manual | LSP (native) |

### 1.10 Lessons for Hugin

1. **A diagnostic is a typed value whose fields are the data it needs** (rustc, GHC, Elm, Roc,
   swift-syntax). Rendering, JSON, LSP and tests are views of that value.
2. **Keep the wording next to the data.** rustc's move to Fluent and back is the clearest experiment
   available: externalised messages cost every contributor, every day, for a translation benefit that did
   not materialise. TypeScript's central file shows the other cost: keying by text multiplies codes.
3. **One registry of codes, append-only, never reused**, with retired entries kept (rustc, dotty, GHC,
   Lean). Make duplicates impossible by construction (GHC's injective type family; in Scala, an `enum` with
   a uniqueness check).
4. **Code granularity is a separate decision from type granularity.** Several constructors may share a
   code (GHC's `ConRecursInto`, rustc's shared codes), but one code should name one *concept*. It should
   not name one sentence (TypeScript) or a whole phase (Hugin's E0202 today).
5. **Carry provenance.** Elm's `Expected`/`Context` shows that the best messages come from recording why
   something was expected. Put reasons in the value as data, not as preformatted strings.
6. **Explanations are documentation with tested examples.** rustc's `compile_fail,EXXXX` doctests, dotty's
   `sc:fail`, and rustc's lint `{{produces}}` all compile the examples, so the documentation cannot drift.
7. **Suggestions need applicability**, so that `fix` commands and editors can tell "apply blindly" from
   "offer".
8. **Test code and position independently of wording**: rustc's `//~ ERROR`, Swift's `expected-error` and
   dotty's `// error`. Keep golden files for the full rendering, and verify that applying suggestions
   yields a program that compiles (rustfix).
9. **An escape hatch is needed for migration, and it must be measured.** dotty's `NoExplanation` and GHC's
   `UnknownDiagnostic` show that an unmeasured escape hatch becomes permanent.
10. **Warnings should be lints with names and levels**, not hard-coded (rustc, Swift groups).

---

## Part 2 — Hugin today

### 2.1 What already works

* **Rendering** (`src/main/scala/hugin/util/Diagnostics.scala`, 185 lines). The output is rustc-style: a
  primary label (`^^^`) and secondary labels (`---`) on one marker row, labels in other files (`::>`),
  notes and helps, and a meta-level expansion chain (`Origin`/`TraceFrame`, comparable to rustc's macro
  backtrace). It renders with or without colour.
* **Suggestions as edits** (`Suggestion(message, span, replacement)`). They may lie in another file, and
  `withSuggestion` drops them for generated code that has no source text. There are 11 call sites, among
  them adding `%complete l` to a signature, adding the missing labels or `..`, and renaming a singleton
  to `_`.
* **A rustfix-like test.** `src/test/scala/hugin/compiler/SuggestionsSuite.scala` (11 tests) applies a
  suggestion and asserts that the diagnostic is gone.
* **The LSP** (`src/main/scala/hugin/lsp/Features.scala`) maps the primary label to the range, secondary
  labels and the expansion chain to `relatedInformation`, the code to `code`, W0002 and W0003 to the
  `Unnecessary` tag, and suggestions to `quickfix` code actions, the first one marked preferred.
  `tests/lsp/diagnostics_and_fixes.in` covers this.
* **Incrementality.** Diagnostics are values pushed to query accumulators
  (`src/main/scala/hugin/query/FileDiagnostics.scala`), deduplicated by the `Reporter` and ordered per
  file.
* **Golden tests.** `tests/neg` has 101 files, among them 49 `.check` files. Every one of the 48
  codes appears in at least one `.check` (checked with grep on `error[E…]`/`warning[W…]`). The rule in
  `docs/REDESIGN.md` §12 asks for exactly this, but nothing enforces it.
* **A catalog and `hugin explain`.** `src/main/scala/hugin/util/ErrorCodes.scala` holds 48
  `(code, title, explanation)` tuples. `ErrorCodesSuite` checks, with a regex over the sources, that the
  catalog and the emitted codes agree, and that codes are unique and sorted.
* **A precursor of a typed diagnostic.** `TerminationFailure` in `obj/check/Termination.scala` is a case
  class with `message`, `span`, `label`, `secondary`, `notes` and `helps` and a `diagnostic` method. It is
  untyped in its content, but it already separates "what failed" from "report it".

### 2.2 Numbers

Code literals outside the catalog, from `grep -E '"[EW][0-9]{4}"'` over `src/main/scala`: **182
occurrences of 48 distinct codes in 23 files**, at about 210 calls of `Diagnostic.error`,
`Diagnostic.warning`, `ctx.error` or a local `err(...)` helper.

| area | files | occurrences | codes | fate in REDESIGN §9 |
|---|---|---:|---|---|
| syntax (`Lexer`, `Parser`) | 2 | 18 | E0001–E0004 | keep, extend |
| meta naming (`Namer`) | 1 | 12 | E0004 E0102 E0103 | adapt |
| meta typing (`meta/typer/*`: `ObjectCode` 36, `TypeElaboration` 20, `MetaExpressions` 15, `Typer` 11, `Declarations` 10, `TyperBase` 3) | 6 | 95 | E0001 E0004 E0101–E0107 E0201–E0210 E0301 E0302 E0306 E0307 E0404 E0406 E0701 W0002 W0003 W0005 | **rewrite** (B1–B3) |
| meta evaluation (`MetaEval` 8, `Monomorphize` 4) | 2 | 12 | E0202 E0205 E0206 E0209 E0402 E0501 E0701 | **rewrite** |
| object typing (`ObjTyper` 22, `Directives` 5, `Moding` 4, `ConstFold` 1) | 4 | 32 | E0208 E0303–E0305 E0401–E0405 E0501–E0503 E0701 W0001 | keep / adapt |
| checks (`Termination` 2, `Completeness` 2, `Stratify` 1) | 3 | 5 | E0601–E0604 | **rework** (A1) / keep |
| transforms (`Demand`) | 1 | 1 | E0504 | **delete** (C3) |
| driver, runtime, REPL, LSP (`Libraries` 3, `FactLoader` 1, `Session` 1, `Features` 1) | 4 | 6 | E0108 E0801 W0002 W0003 | keep |

**About 65% of the occurrences (119 of 182) are in the meta level that Phase B deletes.** Migrating them
would be wasted work. The new elaborator should emit typed diagnostics from day one.

Codes are spread across files: E0202 occurs 34 times in 4 files, E0103 15 times in 5 files and E0207 12
times in 5 files. E0001 (syntax) is also raised by the meta typer (`MetaExpressions.scala:108`), and
E0501 (moding) by `MetaEval`.

### 2.3 Problems

1. **Codes are untyped strings.** `Diagnostic.code: Option[String]`, and `ctx.error(code: String, …)`.
   A typo compiles. The only guard is `ErrorCodesSuite`'s regex, which a code built dynamically or
   mentioned in a comment would fool. Properties of a code live elsewhere: `Features.scala:114` hard-codes
   `Set("W0002", "W0003")` as "unnecessary".
2. **Codes are too coarse to mean anything.** E0202 "stage error" carries **25 distinct message texts**.
   Some are stage errors ("splice of a value that is not code"). Others are shape errors ("an aggregate
   must be bound to a variable", "`as` in a body applies to a relation atom", "a record can only follow a
   relation"), and one of them literally reads "stage error". E0101 "unresolved name" also covers "`a` has
   no member `internal`". A user who looks up a code learns little, and a test that expects E0202 checks
   little.
3. **The same error is worded differently at different call sites.** In `ObjectCode.scala`, "expected a
   term" is the headline at three call sites (lines 104, 111 and 125): one has a label and a note, one
   has only a label, and one has neither. At two other sites (lines 70 and 118) it is the label of a
   different headline. E0101's spelling help reads "a declaration with a similar name exists: `x`" in
   `TyperBase.scala:117` but "did you mean `x`?" in `MetaExpressions.scala:197`. The second is the form
   rustc's style guide advises against.
4. **Reasons are preformatted strings.** For example, `Completeness` builds ``"`a` depends positively on
   `b`; `b` is declared %open"`` as a `String`. The diagnostic cannot point a secondary label at the
   `%open` directive or the dependency edge, and the LSP cannot link to them.
5. **There is no inventory.** "Which diagnostics can the completeness check produce?" or "what data does
   E0604 carry?" can only be answered by grep. The catalog's explanations are one or two sentences without
   examples, and they cite spec sections ("Section 6.4", "Definition 6.6"). Section references also appear
   in **18 message strings in 13 files**, and Phase D will renumber those sections.
6. **Suggestions have no applicability.** "replace `Y` with `_`" (safe) and "replace with `road`" (a guess)
   look the same to a tool. The LSP marks the *first* suggestion as preferred, whatever it is. A
   `hugin fix` command cannot be written safely.
7. **Diagnostics are text for tools.** The LSP concatenates the message, the primary label, `note: …` and
   `help: …` into one string. There is no `codeDescription` link to an explanation. There is no JSON
   output for scripts or CI annotations. Tests can only assert on codes and strings.
8. **Warnings are not lints.** `--no-warnings` turns off all four warnings or none of them. There are no
   names, levels or per-site silencing.
9. **Deduplication keys on text**: `(code, message, span)` in `Reporter`.
10. **Small quality bugs that a central definition would fix once.** In `tests/neg/names.check`, `raod` is
    not matched to `road`: Levenshtein counts the transposition as 2, which exceeds the threshold
    `len/3 = 1`. Spelling suggestions are computed in two places with two thresholds.

---

## Part 3 — Design for Hugin

### 3.1 Goals and non-goals

**Goals**

* A call site reports a *value*: `ctx.report(CheckError.NegatedIncomplete(rel, use, site, why))`.
* The Scala compiler enforces that every diagnostic has a registered code, that its arguments have the
  right types, and that its wording is in one place.
* "What does phase X produce?" is answered by one source file.
* Rendering, JSON, LSP and `hugin explain` are derived from the same value.
* Tests enforce that every active code has a negative test, an explanation and a compiled example.
* New code (A1, A2, B1–B3, C) uses the new system from its first commit, and nothing else has to be
  migrated first.

**Non-goals (for now):** translation; user-defined diagnostics from meta code (worth revisiting with
Phase C's user directives, see [§3.14](#314-open-questions)); a lint configuration language beyond
command-line flags.

### 3.2 Architecture

```
 call site                         util/diagnostics/ (new)                      consumers
 ─────────                         ───────────────────────                      ─────────
 ctx.report(                ┌────► Problem (trait): code, primary, message,     DiagnosticRenderer (terminal)
   CheckError.Negated...)   │        labels, notes, helps, suggestions         JsonEmitter (--error-format=json)
        │                   │               │ toDiagnostic                      lsp.Features (LSP diagnostics,
        ▼                   │               ▼                                      codeDescription, code actions)
 enum CheckError ───────────┘      Diagnostic (data): Code, Severity, Msg,      Reporter / FileDiagnostics
   extends Problem                   labels, notes, helps, Suggestion(          tests (codes, structure, goldens)
   (one enum per phase:              edits, Applicability), origin
   the inventory)                           ▲
                                   enum Code: number, title, phase, level,  ◄── docs/errors/EXXXX.md
                                     flags, status (the registry)                (explanations; examples compiled
                                                                                   by ExplanationsSuite)
```

`Diagnostic` stays a plain immutable value, close to today's: it is what accumulators, the reporter and the
LSP handle. The typed `Problem` is what call sites build and what tests can observe. It is converted at
`report` time, so the incremental database never stores compiler symbols inside diagnostics (see
[§3.4](#34-problems-per-phase-families-the-inventory)).

### 3.3 Codes: `enum Code`, the registry

One enum replaces `ErrorCodes.all`. The numbers keep their current values, which users, tests and
`docs/REDESIGN.md` refer to.

```scala
package hugin.util.diagnostics

enum Phase:
  case Syntax, Names, MetaTyping, Records, ObjectTyping, Moding, Checks, Directives, Input, Driver

enum Level:
  case Error, Warning, Allow     // default level; lints may be re-levelled (§3.8)

enum Status:
  case Active
  case Retired(since: String)    // never removed, never reused (rustc, dotty, GHC)

/** A diagnostic code. The registry: every code Hugin has ever emitted, append-only. */
enum Code(
    val number: Int,
    val level: Level,
    val phase: Phase,
    val title: String,                     // catalog title, lowercase, no period
    val lint: Option[String] = None,       // lint name for warnings ("singleton_variables")
    val unnecessary: Boolean = false,      // LSP DiagnosticTag.Unnecessary
    val status: Status = Status.Active
):
  case E0001 extends Code(1, Level.Error, Phase.Syntax, "syntax error")
  // ...
  case E0101 extends Code(101, Level.Error, Phase.Names, "unresolved name")
  case E0602 extends Code(602, Level.Error, Phase.Checks, "negation or aggregation over an incomplete relation")
  case W0002 extends Code(2, Level.Warning, Phase.Names, "singleton variable",
    lint = Some("singleton_variables"), unnecessary = true)
  // ...
  case E0406 extends Code(406, Level.Error, Phase.ObjectTyping, "data constructor used as a relation",
    status = Status.Retired("redesign C3"))   // when the data/fact split is deleted

  def id: String = (if level == Level.Error then "E" else "W") + f"$number%04d"
  def explanationResource: String = s"/hugin/errors/$id.md"

object Code:
  def parse(s: String): Option[Code] = values.find(_.id.equalsIgnoreCase(s))
```

Rules:

* **Uniqueness.** A test asserts that the `id`s are distinct; the case names (`E0602`) make a clash
  visible in review. In Scala this is as strong as GHC's injective family, at test time instead of
  compile time.
* **Numbering.** The existing hundreds per phase stay, because they give users a phase hint, which GHC's
  random numbers do not. A new code takes the next free number in its phase's block, so the
  `ErrorCodesSuite` "sorted" check becomes "sorted within a phase". A retired number is never reused.
* **One code per concept.** Several `Problem` cases may share a code if one explanation covers them all.
  A code is split when its explanation would need an "or" between unrelated causes. E0202 is the example
  in [§3.12](#312-migration-plan) (step M4).
* **Lints** keep their `W` code for `hugin explain` and gain a name for flags.

### 3.4 Problems per phase: families, the inventory

Each phase declares its problems as **one enum whose cases are case classes**: the phase's inventory.

```scala
/** Something a phase reports. Each enum of problems is the inventory of one phase. */
trait Problem:
  def code: Code
  def primary: Span                         // the smallest span that shows the problem
  def message: Msg                          // headline: lowercase, no period
  def primaryLabel: Msg = Msg.empty         // what is wrong *here*
  def labels: List[(Span, Msg)] = Nil       // secondary: related places
  def notes: List[Msg] = Nil                // facts: why it is an error
  def helps: List[Msg] = Nil                // what to do
  def suggestions: List[Suggestion] = Nil   // edits, with applicability
  def severity: Severity = code.level.toSeverity

  final def toDiagnostic: Diagnostic =
    Diagnostic(severity, code, message, Label(primary, primaryLabel, primary = true) ::
      labels.map((s, m) => Label(s, m, primary = false)), notes, helps, suggestions = suggestions)
```

The package layout follows the phases (inventory files are named `*Problems.scala`):

| file | enum | codes |
|---|---|---|
| `syntax/SyntaxProblems.scala` | `SyntaxError` | E0001–E0005 |
| `meta/NameProblems.scala` | `NameError` | E0101–E0108 |
| `core/…Problems.scala` (new elaborator, B1–B3) | `ElabError`, `StageError`, `TotalityError` | E02xx, new codes |
| `obj/typing/TypingProblems.scala` | `ObjTypeError`, `RecordError` | E03xx, E04xx |
| `obj/typing/ModingProblems.scala` | `ModingError` | E05xx |
| `obj/check/CheckProblems.scala` | `CheckError` (stratification, completeness), `TerminationError` | E06xx |
| `obj/typing/DirectiveProblems.scala` | `DirectiveError` | E07xx |
| `runtime/InputProblems.scala` | `InputError` | E08xx |
| `util/diagnostics/Lints.scala` | `Lint` | W0xxx |

Guidelines for the case classes:

* **Fields are the data, not the text.** Use symbols (`RelSym`, `Sym`), types (`OType`, the new core
  types), spans, small enums of reasons, and lists of these. Do not use preformatted strings. A reason with
  structure becomes its own enum, as Elm's `Expected`/`Context` does
  ([§3.15](#315-samples-two-current-diagnostics-rewritten), `Incompleteness`).
* **Wording is a method of the case**, written once. Variants that differ only in wording become a field
  (`site: NegSite` = rule or query), not a new case.
* **Conversion is eager.** `ctx.report(p: Problem)` calls `p.toDiagnostic` immediately. The `Diagnostic`
  holds only strings, spans and a `Code`, so the query accumulators stay small and compare structurally, as
  they do now. Tests can additionally capture the `Problem` values through a reporter hook (`Reporter(
  onProblem = …)`), which is off in production.
* **Exhaustiveness helps.** A `match` over a phase's enum (in the coverage test, in `hugin explain --list`)
  is checked by the Scala compiler, so a new case cannot be forgotten.

### 3.5 Messages: `Msg` and a typed interpolator

Today a message is a `String` whose code fragments are backticked by hand. The proposal is a small
structured message, in the spirit of Roc's semantic `Document` and dotty's `Shown`:

```scala
enum Seg:
  case Text(s: String)
  case Code(s: String)          // source code, names, directives: rendered in backticks / bold
  case Type(s: String)          // a printed type: rendered as code, may get "where" notes later

final case class Src(text: String)   // program text
final case class Lit(text: String)   // prose

final case class Msg(segs: Vector[Seg]):
  def plain: String = segs.map {
    case Seg.Text(s) => s
    case Seg.Code(s) => s"`$s`"
    case Seg.Type(s) => s"`$s`"
  }.mkString

/** How a value appears in a message. */
trait DiagArg[-A]:
  def seg(a: A): Seg

object DiagArg:
  given DiagArg[RelSym] = r => Seg.Code(r.name)
  given DiagArg[Sym]    = s => Seg.Code(s.name)
  given DiagArg[OType]  = t => Seg.Type(t.show)
  given DiagArg[Int]    = n => Seg.Text(n.toString)
  given DiagArg[Src]    = c => Seg.Code(c.text)    // program text that is not a symbol: `%open`
  given DiagArg[Lit]    = l => Seg.Text(l.text)    // explicit opt-in for plain words
  // no instance for String: a bare string must say whether it is code or prose

opaque type Arg = Seg
object Arg:
  given [A: DiagArg]: Conversion[A, Arg] = summon[DiagArg[A]].seg(_)

extension (sc: StringContext) def msg(args: Arg*): Msg = ...
```

At a call site this reads ``msg"negation over the incomplete relation $rel"``. Because `RelSym` renders as
`Seg.Code`, the backticks are added by the renderer, not by the author. Interpolating a `String` does not
compile: the author writes `Src(s)` (program text) or `Lit(s)` (prose). That enforces the style rule that code is always
marked. The pattern (an opaque target type plus a `given Conversion` in its companion, and `Shown*`
varargs) is what dotty uses for `i"..."`/`em"..."`. Step M1 must confirm that it compiles cleanly under
Hugin's `-feature -Werror`, and otherwise fall back to an explicit `.arg` extension.

Renderers then treat segments differently. The terminal renders `Code` in bold inside backticks. JSON
emits the plain text with backticks (for compatibility) and may later add the segments. The LSP sends
plain text, because `Diagnostic.message` is not Markdown. In `hugin explain` and hovers, code is rendered
as Markdown code.

### 3.6 Suggestions with applicability

```scala
enum Applicability:
  case MachineApplicable   // preserves meaning or is certainly intended; `hugin fix` applies it
  case MaybeIncorrect      // a plausible guess (spelling corrections); offered, never auto-applied
  case HasPlaceholders     // contains `_` holes or `...` the user must fill in

final case class Edit(span: Span, replacement: String)
final case class Suggestion(message: Msg, edits: List[Edit], applicability: Applicability)
```

* **Multi-part edits.** A suggestion may need several edits, as rustc's multipart suggestions do: for
  example, wrapping a term in parentheses, or adding `%complete l` to a signature in another file *and*
  renaming at the use site.
* **Defaults.** There is no `Unspecified` and no default. Every suggestion states its applicability,
  because the most useful property is that `MachineApplicable` can be trusted.
* **Today's 11 suggestions**, classified:

  | suggestion | applicability |
  |---|---|
  | add `.` at end of item | `MachineApplicable` |
  | replace `Y` with `_`, rename to `_Y` | `MachineApplicable`, `MaybeIncorrect` |
  | add missing labels as `_` / ignore with `..` | `MachineApplicable` |
  | add `%complete l` to the signature | `MachineApplicable` |
  | declare `%fact`, mark `%abbrev`, declare `%directive` | `MachineApplicable` |
  | replace with similar name (`road`) | `MaybeIncorrect` |

* **LSP.** Every suggestion becomes a `quickfix` code action. `isPreferred` is set only on a
  `MachineApplicable` one (the first, if there are several).
* **CLI (step M5).** `hugin fix FILE` applies `MachineApplicable` suggestions in a loop until there are
  none left or a fixed point is reached, as `cargo fix` does. `--error-format=json` exposes all of them.

### 3.7 Where the wording lives: Scala, not resource files

| | Scala-side (in the case class) | Externalised (Fluent `.ftl` / JSON / `.def`) |
|---|---|---|
| editing a diagnostic | one place: data, wording, labels, suggestions | two places, kept in sync by ids |
| argument types | checked by Scala (`DiagArg`) | checked by a generator or at runtime |
| conditional wording (plural, rule vs query) | ordinary Scala `match` | a template language (`%select`, Fluent selectors) |
| navigation (go to definition, find usages) | works | needs custom tooling |
| wording review in one place | per phase file (the inventory) | one file |
| translation | would need extraction later | ready |
| evidence | rustc moving back inline (MCP #959, 2026); dotty, Elm, GHC, Roc, Gleam are all inline | TypeScript (code explosion), Swift (cryptic `%select`) |

**Decision.** Wording stays in Scala, in the problem's methods. Hugin is a reference implementation whose
diagnostics cite language concepts, it has no translation requirement, and the evidence is one-sided. A
reviewer reads a phase's wording in one file, the inventory, which is what a resource file would have
offered. Should translation ever matter, `Msg` with named arguments can be extracted mechanically.

**Long explanations** are different: they are prose documents with code blocks, read by users on the web
and in `hugin explain`. They live as Markdown in **`docs/errors/EXXXX.md`**, one file per code (as in
rustc, dotty and Lean), and are packaged as resources (`/hugin/errors/EXXXX.md`) by an sbt resource
mapping, so that `hugin explain` works offline.

### 3.8 Lints

The four warnings become lints: `W0001 undefined_constant_expressions`, `W0002 singleton_variables`,
`W0003 unused_definitions`, `W0005 empty_formula_functions`. Each has a default level in its `Code`.
Command-line flags `-W name`, `-A name` and `-D name` (warn, allow, deny), plus `--deny-warnings`, change the
level (*as built in M5*: `enum Lint` in `util/diagnostics/Lints.scala`, `LintLevels`; `--no-warnings` was
removed rather than kept as an alias; every shown lint carries a note naming it and the origin of its
level). An in-source attribute (`%allow
singleton_variables.` on an item) is left for the redesign's directive work (C2), where directives become
meta functions. New warnings, for example from the size-change checker, are declared as lints from the
start.

### 3.9 Explanations with compiled examples

Template, following rustc's RFC 1567 and dotty's error-code pages, shown here for E0602:

````markdown
# E0602: negation or aggregation over an incomplete relation

A rule or query negates or aggregates over a relation whose facts may be incomplete.

## Example

```hugin fail=E0602
n : int -> rel.
%open n.
n 0.
?- C = count { X | n X }.
```

## Why this is an error

The absence of a fact of an incomplete relation means "unknown", not "false" ...
(the language reference: completeness discipline)

## How to fix it

```hugin
n : int -> rel.
n 0.
?- C = count { X | n X }.
```

## Related

E0601 (stratification cycle), `%complete` in signatures (E0210).
````

* **Fenced blocks are tested.** `ExplanationsSuite` reads every `docs/errors/*.md`. A ` ```hugin fail=EXXXX `
  block must compile with **an error of that code**, and that error must be its first one. A ` ```hugin `
  block must compile without errors. Blocks for retired codes are tagged `ignore`. This is rustc's
  `compile_fail,EXXXX` and dotty's `sc:fail`.
* **Explanations do not cite section numbers** in messages. They may link to the language definition by
  stable anchor names. That fixes problem 5 of [§2.3](#23-problems) before Phase D renumbers the sections.
* **`hugin explain E0602`** prints the file, rendered for the terminal. `hugin explain --list` prints the
  registry grouped by phase, with each code's title and status: the browsable inventory.

### 3.10 JSON output and LSP

**JSON.** `hugin check --error-format=json` prints one object per line. The schema is versioned, so that
tools can rely on it (GHC's practice), and modelled on rustc's:

```json
{"version":1,"code":{"id":"E0602","title":"negation or aggregation over an incomplete relation",
 "explanation":"docs/errors/E0602.md","url":"https://k0uks1.github.io/hugin/reference/errors/E0602.html"},"level":"error",
 "message":"query negates or aggregates over the incomplete relation `n`",
 "spans":[{"file":"q.hgn","start":{"line":7,"col":20},"end":{"line":7,"col":23},"byteStart":91,"byteEnd":94,
           "primary":true,"label":"used negatively"},
          {"file":"q.hgn","start":{"line":2,"col":1},"end":{"line":2,"col":11},"primary":false,
           "label":"`n` is declared %open here"}],
 "notes":["queries may mention incomplete relations only positively"],"helps":[],
 "suggestions":[],"origin":[],"rendered":"error[E0602]: ..."}
```

`rendered` is the terminal rendering without colour, so a tool can show exactly what the CLI shows. JSON
lines are also the format for CI annotations and for any future build-tool integration.

**LSP** (`lsp/Features.scala`):

| LSP field | from |
|---|---|
| `code` | `code.id` |
| `codeDescription.href` | the explanation's page in the error index of the language reference, `<site-url>errors/E0602.html` (implemented: `site-url` is `reference/site-url.txt`, packaged at build time; `url` in the JSON, the last line of `hugin explain`) |
| `message` | message, then the primary label; notes and helps follow as now (LSP has no structure for them) |
| `tags` | `Unnecessary` from `code.unnecessary`, replacing the hard-coded set in `Features.scala`; `Deprecated` when a lint says so |
| `relatedInformation` | secondary labels, then the expansion chain (as now) |
| `data` | `{ "code": "E0602", "suggestions": [...] }`, so `codeAction` does not have to recompile |
| code actions | one `quickfix` per suggestion; `isPreferred` only for `MachineApplicable`; a "Fix all `singleton_variables` in file" source action for machine-applicable lints (TypeScript's `fixId`) |

### 3.11 Testing strategy

Five layers. Each layer tests something the others do not.

1. **Golden UI tests (keep).** `tests/neg/*.check` holds the full rendering and remains the review surface
   for wording. `HUGIN_UPDATE_CHECKS=1` re-blesses, as now.
2. **Inline code annotations (new, cheap).** In `tests/neg/*.hgn`, a comment `(*~ E0602 *)` at the end of a
   line, or `(*~^ E0602 *)` for the line above, states that this code is reported on that line. The
   golden runner checks that the annotations match **exactly** the codes and lines reported, independently
   of wording, as rustc's `//~` and Swift's `expected-error` do. A wording change then touches only
   `.check` files, while a change of code or position fails loudly. Existing tests gain annotations as
   their phase migrates.
3. **Structural unit tests.** With the reporter hook, a suite asserts on the problem value, for example
   `assertEquals(problems(src), List(CheckError.NegatedIncomplete(n, …)))`, instead of on strings. This
   suits the new elaborator's unit tests (B1, B2).
4. **Fix tests (generalising `SuggestionsSuite`).** `tests/fix/X.hgn` with `X.fixed`: apply every
   `MachineApplicable` suggestion, compare with `X.fixed`, and require that `X.fixed` compiles without the
   original code (rustfix). `MaybeIncorrect` suggestions keep unit tests as now.
5. **A coverage test** (`DiagnosticsCoverageSuite`, replacing `ErrorCodesSuite`), with no regex over the
   sources:
   * every `Code` with `status == Active` has a `docs/errors/<id>.md` with at least one `fail=<id>`
     example, and every Markdown file corresponds to a `Code`;
   * every active code occurs in at least one `tests/neg` annotation or `.check` file. This is GHC's
     "codes" test and the rule of REDESIGN §12, now enforced;
   * every retired code occurs in **no** `.check` file;
   * `id`s are unique, and numbers are sorted within each phase;
   * the number of `Problem.Legacy` call sites (see [§3.12](#312-migration-plan)) is at most a recorded
     bound, and the bound may only go down.

### 3.12 Migration plan

Each step is one PR into the development branch, keeps CI green, and lists its acceptance criteria. The
order follows REDESIGN §10: typed infrastructure first, then the phases being rewritten, then the stable
phases. The old meta typer is never migrated.

**M0 — This document.** *Accept*: reviewed on #41; decisions on [§3.14](#314-open-questions) recorded
in issue #41.

**M1 — Minimal typed core** (in `util/diagnostics/`; no change in output).
* Add `enum Code` with all 48 current codes, titles and properties moved from `ErrorCodes.all`, and
  `ErrorCodes.explain` reimplemented on top of it.
* Add `Msg`, `DiagArg` and `msg"…"`; the `Problem` trait; `Applicability`; `Suggestion` with `edits` and
  `applicability`.
* Change `Diagnostic.code` to `Option[Code]`.
* Add the legacy escape hatch: `Problem.Legacy(code: Code, message: String, …)` and an overload
  `ctx.error(code: Code, …)`. Every existing `"E0204"` literal becomes `Code.E0204` (a mechanical
  rewrite of the 182 occurrences), so the compiler now checks codes everywhere.
* Classify the existing 11 suggestions (table in [§3.6](#36-suggestions-with-applicability)), and change
  `Features.isPreferred` and `unnecessary` to use them.
* *Accept*: no string code literal remains outside `Code` (a test greps for it); all `.check` files are
  unchanged; `ErrorCodesSuite` is replaced by the uniqueness, sorting and catalog parts of the coverage
  test; the build is clean under `-feature -Werror`; the legacy bound is recorded.

**M2 — Explanations and JSON.**
* Move the 48 explanations to `docs/errors/EXXXX.md` with examples, and add `ExplanationsSuite`.
* Add `hugin explain --list`, `--error-format=json`, LSP `codeDescription` and `data`.
* Remove spec section numbers from messages: 18 strings, whose notes move to the explanations.
* *Accept*: every active code has an explanation with a failing example that compiles to that code; JSON
  output is covered by golden tests (`tests/json`); the LSP transcript test shows `codeDescription`;
  `.check` changes are limited to the removed section references and are listed in the PR.

**M3 — Phases being rewritten: termination (A1) and new checks (A2).**
* Introduce `TerminationError` (replacing `TerminationFailure`) and `CheckError` (stratification,
  completeness). The reasons become data: the cycle as a list of `(RelSym, Span)`, the invention site,
  which direction failed (§4.4 of REDESIGN), and `Incompleteness`.
* New A2 codes (bound-column consistency) are typed from the start.
* Add inline annotations to the `tests/neg/a0[5-8]_*` and `t_termination_*` tests.
* *Accept*: no `Legacy` uses remain in `obj/check`; coverage holds; every changed `.check` is listed and
  reviewed; the size-change checker's diagnostics have structural tests.
* *Done* (#41): `obj/check/TerminationProblems.scala` (`TerminationError`, with the reasons `Invention`,
  `DescentFailure`, `Measure`, `MissingGuard` in `TerminationReasons.scala`), `BoundColumnProblems.scala`
  (`BoundColumnError`, `Inconsistency`) and `obj/transform/DemandProblems.scala` (`DemandError`); no
  `Legacy` use remains outside the old meta typer and the new elaborator; inline annotations are checked
  by `GoldenTests` (`tests/neg/a0[5-8]_*`, `b_*`, `t_termination_*`); structural tests in
  `TerminationProblemsSuite` and `BoundColumnProblemsSuite`.

**M4 — The new meta level (B1–B3) and directives (C2).**
* `core/*Problems.scala` from the first commit: `ElabError`, `StageError`, `TotalityError` (coverage,
  structural termination) and `NameError`.
* Re-home E0202's concepts as separate codes, for example "expected a term" / "expected a formula"
  (shape), "splice of a non-code value" (stage proper) and "aggregate must be bound" (syntax-level). The
  old E0202 stays as a retired code if its meaning does not survive. Unify the spelling-suggestion helper
  (one threshold, transposition-aware), and split "no member" out of E0101 into its own code.
* *Accept*: the new elaborator has zero `Legacy` uses; when B3 deletes `meta/typer`, `MetaEval` and
  `Monomorphize`, the legacy count drops by those files' share, and the bound is lowered in the same PR;
  B3's "same goldens" criterion is met with every changed `.check` reviewed.
* *Done* (with B3): the meta level reports typed problems only (`core/elab/ElabProblems`,
  `TypeProblems`, `ClauseProblems`; staging uses `TypeProblem.NotStaged`). The old meta typer, MetaEval
  and Monomorphize are deleted; E0106, E0201, E0203 and E0209 are retired (their concepts are E0901,
  E0902 and E0909 of the meta level, or gone), E0105 names a self-referential definition, E0916 the
  binders of a declared type used in its definition. Not done: E0202's concepts are not split, "no
  member" stays E0906 (the meta level's "no field") rather than a new code.

**M5 — Stable phases and tools.**
* Migrate `syntax/`, `obj/typing/` (`ObjTyper`, `Moding`, `Directives`, `ConstFold`), `compiler/Libraries`
  and `runtime/FactLoader` to their enums.
* Add lints with `-W`/`-A`/`-D`; add `hugin fix` and `tests/fix`.
* *Accept*: the legacy count is 0, `Problem.Legacy` is deleted, and `Diagnostic.code` becomes `Code`, no
  longer an `Option`, except for internal compiler errors, which get a code of their own (`F0001`). Every
  machine-applicable suggestion has a fix test.
* *Done so far* (#41): lints, `-W`/`-A`/`-D`/`--deny-warnings`, `hugin fix` (`util/diagnostics/Fixes.scala`,
  `cli/Fix.scala`) and `tests/fix` with one test per machine-applicable suggestion. The stable phases
  have no `Legacy` use left; the remaining 163 are in the old meta typer (deleted by B3) and in the new
  elaborator (`core/`, migrated with M4), so deleting `Problem.Legacy` and making `Diagnostic.code`
  non-optional wait for those.
* *Done* (with B3): `Problem.Legacy` is deleted and `Diagnostic.code` is a `Code`. The messages of the
  tools have codes of their own in the phase `Tools`: E1101 (an invalid REPL command) and E1102 (an
  internal compiler error, reported by the language server; this replaces the planned `F0001`). Codes of
  `Tools` are exempt from golden tests and from examples in their explanations.

**M6 — Consolidation** (with Phase D). Retire E0406 and E0504 when C3 deletes the data/fact split. Review
the wording of the whole inventory against the style guide, phase by phase, as one PR per phase.
* *Done* (retirements, with C3): E0406 (data constructor used as a relation) and E0504 (fact constructor
  built in a moded input) are retired with the data/fact split, E0502 (call without applicable mode) and
  E0503 (input position is not a pattern) with relation modes; their explanations are marked **Retired**
  and their examples `ignore`d, and no `.check` file contains them. The mode checks of E0701 (arity and
  labels of `%mode`), E0208's `%mode` requirement and its fix, E0204's `%fact` field and E0605's moded bound
  relation are gone; a wrong mode of `%demand` is a type error (E0901), and an unbound demanded input is
  E0501 on the generated rule. New under E0103: a primitive operation declared with another type. The
  wording review remains for Phase D.

### 3.13 Style guide

Adapted from rustc's
[diagnostic output style guide](https://rustc-dev-guide.rust-lang.org/diagnostics.html#diagnostic-output-style-guide)
and Elm's tone. This section is normative for new diagnostics.

**Parts of a diagnostic**

| part | says | form | example |
|---|---|---|---|
| headline (`message`) | *what* is wrong, specific to this instance | lowercase, no final period, a statement; names in code style | ``negation over the incomplete relation `n` `` |
| primary label | what is wrong *at this span* | short noun phrase or clause, no period | `used negatively` |
| secondary label | why another place matters | refers back: "declared here", "first declared here", "required by this signature" | `` `n` is declared %open here `` |
| note | a fact that explains *why* it is an error | a sentence without final period; no instructions | `the absence of a fact of an incomplete relation means unknown, not false` |
| help | *what to do* | imperative, or "X exists: `y`"; never "did you mean"; ideally paired with a suggestion | ``remove `%open n` if all facts of `n` are known`` |
| suggestion message | the edit, as a command | imperative verb first | ``add `%complete n` to the signature`` |
| explanation | the concept, with examples | Markdown document | `docs/errors/E0602.md` |

**Rules**

1. Name the user's thing, not the compiler's: "relation", "rule", "query", "constructor", "meta function",
   not internal names such as "RelSym" or "head atom" unless that is the language term.
2. Use code style for every piece of program text. `Msg` makes this automatic.
3. Use "invalid" or a precise word, never "illegal". Do not blame ("you forgot ..."), and do not apologise.
4. Each piece of information appears once: the label does not repeat the headline, and the help does not
   repeat the note.
5. Spans: the smallest that shows the problem. Point at the name, not at the whole item. Use a secondary
   label rather than a note whenever the note would mention a place.
6. Do not cite spec section numbers in messages; explanations may link to them.
7. Use consistent terms, from the glossary of `docs/REDESIGN.md` §13. The same concept gets the same word
   in every phase: "incomplete", "constructive rule", "measure", "stage", "code (⇑τ)".
8. When the compiler guessed, the wording says so ("a relation with a similar name exists: `road`"), and
   the suggestion is `MaybeIncorrect`.
9. Follow-up errors: problems mentioning an error type (`MType.Err`, `OType.Err`) are not reported. Keep
   the existing guards, and make them a property of `report`, as dotty's "non-sensical" messages are.
10. A warning must be silenceable, so it is a lint with a name ([§3.8](#38-lints)).

### 3.14 Open questions

* **Q1 Code granularity of the new elaborator.** How many codes do unification failures get: one
  "type mismatch" with a reason enum (Elm), or several? *Recommendation*: one code per user-facing
  concept, with the reason as a field, and split later only when an explanation needs it.
* **Q2 Named or numbered codes for new families.** Lean and Swift use names (`lean.unknownIdentifier`).
  *Recommendation*: keep numbers for errors, for continuity with the 48 existing codes and the per-phase
  hint, and use names only for lints.
* **Q3 User-defined diagnostics from directives (C2).** A user directive must be able to reject its
  input. That needs a prelude-level `Diagnostic` type (`error : Span -> String -> Diag`) whose diagnostics
  render through the same pipeline under a code for user diagnostics. *Recommendation*: decide when C2 is
  designed, and reserve the `U` prefix now. *Decided in C2:* a directive returns `derror "message"` (a
  `decl`) or an item `ierror "message"`; the message is reported at the directive under E1000. Codes of
  the user's choice (and spans other than the directive's) are left for later; the block E1000–E1099
  is that of directives (E1001–E1003 are the machinery's).
* **Q4 Explanations site.** `codeDescription` links to GitHub until there is a docs site.
  *Recommendation*: make the base URL a setting.

### 3.15 Samples: two current diagnostics rewritten

#### Sample 1: E0101, unresolved name and unknown member

**Today.** There are two call sites with different wording. One is
`meta/typer/TyperBase.scala:114-120`:

```scala
var d = Diagnostic.error("E0101", s"unresolved $what `$name`", span, "not found in this scope")
suggestion(name, sc).foreach { s =>
  d = d.withHelp(s"a declaration with a similar name exists: `$s`")
  if span.text == name then d = d.withSuggestion(s"replace with `$s`", span, s)
}
ctx.report(d)
```

The other is `meta/typer/MetaExpressions.scala:194-197`, which also uses E0101, with a different help
wording and its own threshold:

```scala
var d = Diagnostic.error("E0101", s"`${Printer.show(sel.qual)}` has no member `${sel.name}`", sel.nameSpan, "unknown member")
  .withNote(s"available members: ${fields.map(_._1.name).mkString(", ")}")
sugg.headOption.foreach(s => d = d.withHelp(s"did you mean `$s`?").withSuggestion(s"replace with `$s`", sel.nameSpan, s))
```

**New.** The inventory in `meta/NameProblems.scala`, used by both the old and the new namer:

```scala
enum NameKind(val word: String):
  case Name extends NameKind("name")
  case Relation extends NameKind("relation")
  case Type extends NameKind("type")
  case Directive extends NameKind("directive")

enum NameError extends Problem:
  /** A name that no enclosing scope declares. */
  case Unresolved(name: Ident, kind: NameKind, similar: Option[Sym])
  /** A path `m.x` where the module `m` has no member `x`. */
  case NoMember(module: Path, member: Ident, available: List[Sym], similar: Option[Sym])
  /** A name declared twice in one scope. */
  case Duplicate(name: Ident, first: Span)

  def code = this match
    case _: Unresolved => Code.E0101
    case _: NoMember => Code.E0109          // new code: "no such member" (M4)
    case _: Duplicate => Code.E0102

  def primary = this match
    case Unresolved(n, _, _) => n.span
    case NoMember(_, m, _, _) => m.span
    case Duplicate(n, _) => n.span

  def message = this match
    case Unresolved(n, k, _) => msg"cannot find ${Lit(k.word)} $n in this scope"
    case NoMember(m, x, _, _) => msg"module $m has no member $x"
    case Duplicate(n, _) => msg"$n is declared twice in this scope"

  override def primaryLabel = this match
    case _: Unresolved => msg"not found in this scope"
    case _: NoMember => msg"unknown member"
    case _: Duplicate => msg"redeclared here"

  override def labels = this match
    case Duplicate(_, first) => List(first -> msg"first declared here")
    case _ => Nil

  override def notes = this match
    case NoMember(_, _, avail, _) if avail.nonEmpty =>
      List(msg"available members: ${Names(avail)}")   // Names: DiagArg for a list, comma-separated
    case _ => Nil

  override def helps = similar.toList.map(s => msg"a ${Lit(s.kindWord)} with a similar name exists: $s")

  override def suggestions = (this, similar) match
    case (Unresolved(n, _, _), Some(s)) => List(Suggestion.replace(n.span, s.name, msg"replace with $s",
      Applicability.MaybeIncorrect))
    case (NoMember(_, x, _, _), Some(s)) => List(Suggestion.replace(x.span, s.name, msg"replace with $s",
      Applicability.MaybeIncorrect))
    case _ => Nil

  private def similar: Option[Sym] = this match
    case Unresolved(_, _, s) => s
    case NoMember(_, _, _, s) => s
    case _ => None
```

The call sites become one line each, and they share a single spelling helper (`Spelling.closest`), which
also fixes the `raod`/`road` miss:

```scala
ctx.report(NameError.Unresolved(ident, NameKind.Relation, Spelling.closest(ident.name, sc)))
```

Rendered (`tests/neg/names.hgn`), with the new spelling helper:

```
error[E0101]: cannot find relation `raod` in this scope
 --> tests/neg/names.hgn:7:13
  |
7 | path X Y :- raod X Y.
  |             ^^^^ not found in this scope
  |
  = help: a relation with a similar name exists: `road`
```

The LSP shows the same diagnostic, with a "Replace with `road`" quick fix that is *not* marked preferred
(`MaybeIncorrect`) and a link to `docs/errors/E0101.md`.

#### Sample 2: E0602, negation over an incomplete relation

**Today** (`obj/check/Completeness.scala:17-47`). The reason is a string chain, and the rule and query
variants are two copies with different wording:

```scala
why(e.from) = s"`${e.from.name}` depends positively on `${e.to.name}`; ${why(e.to)}"
...
ctx.report(Diag.query(q)(Diagnostic.error("E0602",
  s"query negates or aggregates over the incomplete relation `${r.name}`", sp, "used negatively")
  .withNote(why(r))
  .withNote("queries may mention incomplete relations only positively (Section 8.5)")))
```

```
error[E0602]: query negates or aggregates over the incomplete relation `n`
 --> tests/neg/completeness_query.hgn:7:20
  |
7 | ?- C = count { X | n X }.
  |                    ^^^ used negatively
  |
  = note: `n` is declared %open
  = note: queries may mention incomplete relations only positively (Section 8.5)
```

**New** (`obj/check/CheckProblems.scala`). The reason is data, so it can point at places:

```scala
/** Why a relation is incomplete: the chain of positive dependencies ending at a declaration. */
enum Incompleteness:
  case Open(rel: RelSym, decl: Span)
  case Via(rel: RelSym, dep: RelSym, edge: Span, next: Incompleteness)

  def origin: Incompleteness = this match
    case Via(_, _, _, n) => n.origin
    case other => other

enum NegSite:
  case InRule, InQuery

enum NegKind:
  case Negation, Aggregation

enum CheckError extends Problem:
  case NegatedIncomplete(rel: RelSym, use: Span, kind: NegKind, site: NegSite, why: Incompleteness)
  case NegativeCycle(cycle: List[(RelSym, Span)], negative: Span)       // E0601
  // ...

  def code = this match
    case _: NegatedIncomplete => Code.E0602
    case _: NegativeCycle => Code.E0601

  def primary = this match
    case n: NegatedIncomplete => n.use
    case c: NegativeCycle => c.negative

  def message = this match
    case NegatedIncomplete(r, _, NegKind.Negation, _, _) => msg"negation over the incomplete relation $r"
    case NegatedIncomplete(r, _, NegKind.Aggregation, _, _) => msg"aggregation over the incomplete relation $r"
    case _: NegativeCycle => msg"cycle through negation"

  override def primaryLabel = this match
    case NegatedIncomplete(_, _, NegKind.Negation, _, _) => msg"negated here"
    case NegatedIncomplete(_, _, NegKind.Aggregation, _, _) => msg"aggregated over here"
    case _ => Msg.empty

  override def labels = this match
    case NegatedIncomplete(_, _, _, _, why) => chain(why)
    case NegativeCycle(cycle, _) => cycle.map((r, sp) => sp -> msg"$r depends on the next relation here")

  override def notes = this match
    case NegatedIncomplete(_, _, _, site, _) =>
      List(msg"the absence of a fact of an incomplete relation means unknown, not false") ++
        (if site == NegSite.InQuery then List(msg"queries may mention incomplete relations only positively")
         else Nil)
    case _ => Nil

  override def helps = this match
    case NegatedIncomplete(_, _, _, _, why) => why.origin match
      case Incompleteness.Open(o, _) => List(msg"open relations are never complete; negate a closed relation instead")
      case _ => Nil
    case _ => Nil

  /** Each step of the reason becomes a secondary label at the declaration or the dependency edge. */
  private def chain(w: Incompleteness): List[(Span, Msg)] = w match
    case Incompleteness.Open(r, d) => List(d -> msg"$r is declared ${Src("%open")} here")
    case Incompleteness.Via(r, dep, e, next) => (e -> msg"$r depends on $dep here") :: chain(next)
```

Call site:

```scala
ctx.report(Diag.query(q)(CheckError.NegatedIncomplete(r, sp, kindOf(occ), NegSite.InQuery, why(r))))
```

Rendered:

```
error[E0602]: aggregation over the incomplete relation `n`
 --> tests/neg/completeness_query.hgn:7:20
  |
2 | %open n.
  | -------- `n` is declared `%open` here
...
7 | ?- C = count { X | n X }.
  |                    ^^^ aggregated over here
  |
  = note: the absence of a fact of an incomplete relation means unknown, not false
  = note: queries may mention incomplete relations only positively
  = help: open relations are never complete; negate a closed relation instead
```

The test gains `(*~ E0602 *)` on line 7, and `docs/errors/E0602.md` (shown in
[§3.9](#39-explanations-with-compiled-examples)) gets a failing and a fixed example, both compiled by
`ExplanationsSuite`. With a chain (`a :- not b`, `b :- c`, `%open c`), the rendering points at both the
dependency edge and the directive, which the string `why` could not do.

---

## Sources

**rustc**
* rustc dev guide: [Errors and lints](https://rustc-dev-guide.rust-lang.org/diagnostics.html) (style
  guide, applicability, lints), [Diagnostic and subdiagnostic structs](https://rustc-dev-guide.rust-lang.org/diagnostics/diagnostic-structs.html),
  [Translation](https://rustc-dev-guide.rust-lang.org/diagnostics/translation.html),
  [Error codes](https://rustc-dev-guide.rust-lang.org/diagnostics/error-codes.html),
  [UI tests](https://rustc-dev-guide.rust-lang.org/tests/ui.html)
* [compiler-team MCP #959: Remove the fluent files](https://github.com/rust-lang/compiler-team/issues/959) (accepted, 2026)
* [`rustc_parse/src/diagnostics.rs`](https://github.com/rust-lang/rust/blob/master/compiler/rustc_parse/src/diagnostics.rs),
  [`rustc_error_codes/src/lib.rs`](https://github.com/rust-lang/rust/blob/master/compiler/rustc_error_codes/src/lib.rs),
  [E0384.md](https://github.com/rust-lang/rust/blob/master/compiler/rustc_error_codes/src/error_codes/E0384.md),
  [`rustc_lint_defs/src/builtin.rs`](https://github.com/rust-lang/rust/blob/master/compiler/rustc_lint_defs/src/builtin.rs)
* [`Applicability`](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_errors/enum.Applicability.html),
  [JSON output](https://doc.rust-lang.org/rustc/json.html),
  [RFC 1567](https://rust-lang.github.io/rfcs/1567-long-error-codes-explanation-normalization.html),
  [error index](https://doc.rust-lang.org/error_codes/error-index.html)

**Scala 3**
* [`reporting/`](https://github.com/scala/scala3/tree/main/compiler/src/dotty/tools/dotc/reporting):
  `Message.scala`, `messages.scala`, `ErrorMessageID.scala`, `MessageKind.scala`, `CodeAction.scala`,
  `Diagnostic.scala`; [`printing/Formatting.scala`](https://github.com/scala/scala3/blob/main/compiler/src/dotty/tools/dotc/printing/Formatting.scala)
* [Error code reference pages](https://github.com/scala/scala3/tree/main/docs/_docs/reference/error-codes)
* [Roadmap for actionable diagnostics](https://contributors.scala-lang.org/t/roadmap-for-actionable-diagnostics/6172),
  [Revisiting Dotty diagnostics for tooling](https://contributors.scala-lang.org/t/revisiting-dotty-diagnostics-for-tooling/5649),
  [Metals 1.1.0](https://scalameta.org/metals/blog/2023/10/17/silver)

**Elm, Roc, Gleam**
* Elm [`Reporting/`](https://github.com/elm/compiler/tree/master/compiler/src/Reporting) (`Report.hs`,
  `Doc.hs`, `Error.hs`, `Error/Type.hs`); [Compiler Errors for Humans](https://elm-lang.org/news/compiler-errors-for-humans);
  [Compilers as Assistants](https://elm-lang.org/news/compilers-as-assistants)
* Roc [`src/reporting/`](https://github.com/roc-lang/roc/tree/main/src/reporting),
  [`src/canonicalize/Diagnostic.zig`](https://github.com/roc-lang/roc/blob/main/src/canonicalize/Diagnostic.zig)
* Gleam [`compiler-core/src/diagnostic.rs`](https://github.com/gleam-lang/gleam/blob/main/compiler-core/src/diagnostic.rs),
  [`error.rs`](https://github.com/gleam-lang/gleam/blob/main/compiler-core/src/error.rs)

**GHC**
* [`GHC.Types.Error`](https://gitlab.haskell.org/ghc/ghc/-/blob/master/compiler/GHC/Types/Error.hs),
  [`GHC.Types.Error.Codes`](https://gitlab.haskell.org/ghc/ghc/-/blob/master/compiler/GHC/Types/Error/Codes.hs)
  (Note [Diagnostic codes])
* [Errors as (structured) values](https://gitlab.haskell.org/ghc/ghc/-/wikis/Errors-as-(structured)-values),
  [Haskell Error Index](https://errors.haskell.org/),
  [JSON diagnostics schema](https://downloads.haskell.org/ghc/9.14.1/docs/users_guide/_downloads/aade9215bf1b87075759c4d918fa42d3/diagnostics-as-json-schema-1_1.json)

**TypeScript, Swift, Lean**
* [`diagnosticMessages.json` (v5.8.3)](https://github.com/microsoft/TypeScript/blob/v5.8.3/src/compiler/diagnosticMessages.json),
  [`codefixes/fixSpelling.ts`](https://github.com/microsoft/TypeScript/blob/v5.8.3/src/services/codefixes/fixSpelling.ts),
  [typescript-go diagnostics generator](https://github.com/microsoft/typescript-go/blob/main/internal/diagnostics/generate.go)
* Swift [`DiagnosticsSema.def`](https://github.com/swiftlang/swift/blob/main/include/swift/AST/DiagnosticsSema.def),
  [`DiagnosticGroups.def`](https://github.com/swiftlang/swift/blob/main/include/swift/AST/DiagnosticGroups.def),
  [swift-syntax `SwiftDiagnostics`](https://github.com/swiftlang/swift-syntax/tree/main/Sources/SwiftDiagnostics)
* Lean [Error explanations](https://lean-lang.org/doc/reference/4.22.0-rc4/Error-Explanations/),
  [`Lean.ErrorExplanation`](https://lean-lang.org/doc/api/Lean/ErrorExplanation.html)

**Hugin**: `src/main/scala/hugin/util/Diagnostics.scala`, `util/ErrorCodes.scala`,
`src/test/scala/hugin/util/ErrorCodesSuite.scala`, `compiler/SuggestionsSuite.scala`, `lsp/Features.scala`,
`query/FileDiagnostics.scala`, `obj/check/{Completeness,Termination}.scala`,
`meta/typer/{TyperBase,MetaExpressions,ObjectCode}.scala`, `tests/neg/`, `docs/REDESIGN.md` §§9, 10, 12.
