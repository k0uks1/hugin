# The parser: architecture review and resilient design (issue #53)

This document reviews the lexer and parser of the reference implementation (`src/main/scala/hugin/syntax`)
as they were before issue #53, compares them with the parsers of production compilers, and records the
design that replaced the error handling: a *resilient* recursive-descent parser in the style of
rust-analyzer and matklad's *Resilient LL Parsing Tutorial*. The accepted language does not change; only
malformed programs are parsed and reported differently.

Contents: [1. Review](#1-review-of-the-parser-before-53) · [2. Established designs](#2-established-designs) ·
[3. Decision](#3-decision) · [4. The resilient parser](#4-the-resilient-parser) ·
[5. Later phases](#5-error-nodes-in-later-phases) · [6. Messages](#6-messages) · [7. Testing](#7-testing)

## 1. Review of the parser before #53

### 1.1 Structure

| file | lines | contents |
|---|---|---|
| `Lexer.scala` | 288 | tokens, keywords, the lexer (errors reported, lexing continues) |
| `Parser.scala` | 553 | token cursor, `%infix` prescan, program and items, panic-mode recovery, declarations, rules, `where`, expressions (precedence climbing), primaries, parentheses, brace disambiguation, module bodies, the slice API |
| `ParserBase.scala` | 21 | abstract hooks the mixins below need from `Parser` |
| `QuoteSyntax.scala` | 89 | holes, lists, rules as expressions |
| `RecordSyntax.scala` | 41 | record types and values |
| `DirectiveSyntax.scala` | 108 | directives, mode items, attached declarations |
| `Trees.scala` | 191 | surface trees |
| `SyntaxProblems.scala` | 148 | E0001–E0004 |
| `Slices.scala` | 82 | item slices for the query database |

The grammar is hand-written recursive descent with a precedence-climbing loop for the binary operators,
which is the right tool for a language whose operators include user-declared ones (`%infix`) and whose
items are distinguished only after their head (`h : τ.`, `h = e.`, `h :- b.`, `h <: τ.`). Splitting
reflection, records and directives into traits was a good start, but:

- **Parser.scala** (553 lines) still mixed six concerns: the cursor and error reporting, the operator
  prescan, the item grammar, the expression grammar, the brace disambiguation and module bodies, and the
  public API. Above the ~400-line maintainability limit of the repository.
- **The mixins talked to the parser through hooks.** `ParserBase` and `DirectiveSyntax` declared abstract
  `tok`, `advance`, `report`, `fail`, `expectPeriod`, `position`, `tokenAt`, `parseAttached` that `Parser`
  implemented as one-line forwarders; a prefix directive handed the declaration it was attached to back
  through a mutable side channel (`followingItems`).

### 1.2 Error handling: control flow by exceptions

Every syntax error was `fail(...)`: report, then `throw ParseError`. The exception was caught at one
place, `parseItemRecovering`, which ran *panic mode*: `sync` recomputed the bracket depth from the item's
start and skipped to a period at depth 0, a `}` closing the enclosing body, or a token in column 0. So:

- **A syntax error discarded the whole item.** `p X :- q X, .` lost the rule; `f : nat -> nat = { … one
  bad member … }.` lost `f` with its type; uses of `f` elsewhere then failed with E0101 (unresolved
  name) — errors that follow from the first one (*cascading*). The IDE lost hover, navigation and
  diagnostics for the region.
- **Recovery granularity was the item.** Nothing recovered inside an argument list, a rule body, a
  record, a list or a bracket. A module body recovered per member, but an unclosed `{` threw past it, so
  the whole enclosing item (body included) was lost.
- **Only one error was repaired**: a missing `.` before an item on a later line (`expect` returned a
  synthetic period). Missing `)`, `]` and `}` were "expected `)`, found …" at some later token, with no
  label on the opening bracket (except `{` at the end of the file) and no fix.
- **Messages** were free-form strings passed to `expect` (``"`.` after declaration"``,
  ``"`,` or `}`"``), with no information on where the construct started; many different mistakes were
  "expected an expression".
- `declHead` reported E0004 and then threw, so `q x : int -> rel.` lost the declaration of `q` as well.
- The `(r).a` projection was not parsed: the lexer makes `.` a selector only directly after a name or
  variable, so `(r).a` was `(r)` followed by the end of the item and a stray `a`.

### 1.3 Other observations

- **`%infix` prescan.** The language says an operator is in effect in the whole file, also before its
  directive, so the operators must be known before parsing; a scan of the token stream for
  `%infix assoc p name` is the simplest correct implementation, and it does not depend on the parse
  succeeding. It stays, as its own small object (`Operators`). The slice API lexes the whole file once
  more for it; the query database memoises it per file text, so this is not a cost worth more code.
- **Lookaheads.** Brace disambiguation (`periodFirst`), lists versus lambdas (`listAhead`), implicit
  binders and attached declarations scan ahead over balanced brackets. They stop at the end of the
  construct (a `}`/`]` at depth 0, a period at depth 0), so they are linear in the construct, not in the
  file, except on malformed input with unbalanced brackets, where they may scan into the following items.
  That only affects which interpretation is tried first; they stay.
- **Slices and incrementality** (`docs/INCREMENTALITY.md`, step 9). The file is parsed as a whole, then
  each top-level item's text is parsed again on its own and used if it parses without diagnostics and is
  congruent to the whole-file item. This needs nothing from the parser except that an item's span covers
  its text, so it is unaffected by the redesign: an item with a syntax error has diagnostics in its slice
  and keeps its whole-file tree.
- **The lexer** is fine: it reports and continues; an unterminated string becomes an `Error` token so the
  parser does not report it again; unknown characters are dropped after a diagnostic.

## 2. Established designs

| | rust-analyzer / matklad's tutorial | Roslyn (C#) | Scala 3 (`Parsers.scala`) | tree-sitter |
|---|---|---|---|---|
| tree | lossless CST (rowan green/red), homogeneous nodes, `ERROR` nodes | lossless, typed red/green; every node always has all children | typed untyped-ASTs (`untpd`), no trivia | concrete tree, `ERROR` and `MISSING` nodes |
| missing token | `expect(T)`: report, consume nothing | a zero-width *missing* token (`IsMissing`) is inserted | `accept(T)`: report "expected", consume nothing | `MISSING` node (cost-based choice) |
| unexpected token | `advance_with_error`: wrap one token in an `ERROR` node | skipped tokens become trivia (`SkippedTokensTrivia`) of the next token | `skip()`: to a stop token at the right nesting depth | `ERROR` node, chosen by cost among parse stacks (GLR) |
| where to resync | per construct: a *recovery set* (FOLLOW of the construct and its ancestors, e.g. `fn` for a parameter list) decides "skip this token" vs "break and let the parent recover" | per list: "is this token something an enclosing construct could use?" | statement separators, closing brackets, indentation (`skip` stops at an outdent) | the GLR parse with the least error cost |
| duplicates | one error per position | one per missing token | `lastErrorOffset`: no second error at or before the last one | — |
| termination | *fuel*: looking at a token costs fuel, consuming restores it; no fuel means "parser is stuck" (a bug) | every loop consumes or breaks | idem | guaranteed by the algorithm |
| incomplete input | — | — | `syntaxErrorOrIncomplete`: in the REPL, the end of the input is "incomplete", not an error | — |

The common principles: **(1)** never abandon a construct: build it with what parsed, a placeholder for
what is missing, and an error node for what was skipped; **(2)** a missing token is reported and
*not consumed* — the parent may need the token that is there; **(3)** each loop decides, for a token it
cannot use, between skipping it (with one error) and returning to its parent, using the tokens its
ancestors can use (*recovery sets*); **(4)** report one error per mistake.

## 3. Decision

**Rewrite the error handling, keep the grammar and the trees.** The grammar code (precedence climbing,
brace disambiguation, the layout of `where` blocks) is correct and its structure fits a recursive-descent
parser; what does not fit resilience is the exception-based control flow, which is spread through every
function (`fail`, `expect`, `ParseError`, `sync`). It is replaced throughout by matklad's resilient-LL
discipline adapted to a typed AST:

- no exceptions for control flow: every parse function returns a tree; syntax errors are reported and
  become **error nodes** (`Trees.ErrorTree`) or placeholders in the tree;
- `expect` reports a missing token and does not consume (insertion); skipping is explicit and bounded by
  recovery sets;
- *fuel* guards every loop against non-progress (a stuck parser is a bug and fails loudly in tests).

**No lossless CST.** A concrete syntax tree with trivia (rowan, Roslyn) pays off for formatters and
syntax-preserving refactorings, neither of which Hugin has or plans. The consumers of the parser are the
elaborator (typed surface trees), the query database (item slices with spans) and the IDE features, which
work on spans and, where they need tokens (completion of the item being typed), on the lexer's tokens. A
homogeneous CST would add a second tree layer and a lowering step for no consumer. Error nodes in the
typed trees give the resilience. Should a formatter be wanted later, the lexer already keeps positions and
the CST can be added below the typed trees then.

**Restructured files** (all well under 400 lines):

| file | contents |
|---|---|
| `Parser.scala` | the parser assembled from its parts; the public API (`parse`, `parseSlice`, `infixOperators`), precedence levels; `Operators`, the `%infix` prescan |
| `ParserBase.scala` | the token cursor, fuel, expected sets, error reporting (one error per region), recovery primitives (skipping, closing delimiters, item ends) |
| `ItemSyntax.scala` | programs and items: declarations, definitions, clauses with `where`, edges, rules, queries; declaration heads |
| `ExprSyntax.scala` | expressions: operators, prefix forms, application, selection, primaries, parentheses |
| `RecordSyntax.scala` | braces: record types and values, implicit binders, module bodies |
| `QuoteSyntax.scala` | reflection: holes, lists, rules as expressions |
| `DirectiveSyntax.scala` | directives, mode items, attached declarations |
| `SyntaxProblems.scala` | the inventory of syntax errors (E0001–E0005) |

The parts are traits over the concrete `ParserBase` class (the cursor is a field, not a set of abstract
hooks), mixed into `final class Parser`. Quoted syntax has its own part (`QuoteSyntax`), and the recovery
primitives (closing a delimiter, ending an item, skipping to a recovery set) are generic, so that explicit
quotes `'{ … }` holding ordinary items (issue #76) can reuse the item loop and its recovery unchanged.

## 4. The resilient parser

### 4.1 Error nodes and missing pieces

- `Trees.ErrorTree(span)` stands for an expression that is missing (zero-width span where it should be) or
  that could not be parsed (the span of the skipped tokens). It is reported when it is created; the tree
  around it is complete.
- `Param.Malformed(tree)` is a declaration parameter that is neither `X` nor `(x : τ)`; the declaration
  keeps its name, its other parameters, its type and its definition.
- A missing delimiter or period is *inserted*: the construct is built as if it were there.
- Items are never discarded for an error inside them. A malformed declaration head that has a name
  (`(p) : rel.`) keeps the name; a head without one (`1 : rel.`) cannot declare anything and only that
  item is dropped. Tokens that cannot start an item are skipped up to the next item start, with one error.

### 4.2 Recovery points and regions

Recovery happens at the innermost construct that can continue:

| construct | separator / end | on an unexpected token |
|---|---|---|
| file, module body, `where` block | items | skip to the next token that can start an item at the start of a line, or a period |
| item | `.` | insert `.` if the next token starts a line (a new item), otherwise report and skip to the period, a column-0 token, or the closing `}` of the body |
| rule heads, rule body, query | `,` `;` | a missing operand is an `ErrorTree`; the next conjunct parses normally |
| argument list | juxtaposition | an argument that is missing is not consumed (the parent decides) |
| `( … )`, `[ … ]`, `{ … }`, aggregate `{ t | b }` | closing delimiter | see 4.3 |
| record type / value, list, higher-order hole | `,` | an entry that fails to parse is an error node; `,` resynchronises |
| declaration | `:` type `<:` `=` | each part is parsed on its own; a broken definition leaves the name and the type |

At most one error is reported per *region*: after an error, further errors are suppressed until the
parser has resynchronised — consumed a separator of an enclosing list (`,` `;` `.`) or a closing
delimiter it was waiting for, or started a new item. This is Scala 3's `lastErrorOffset` rule extended
from positions to regions, and the "one error per mistake" principle of all four designs.

### 4.3 Delimiters

When the parser expects a closing delimiter and finds something else, it looks for the delimiter ahead,
within the current item (over balanced brackets, stopping at a period at depth 0, a token in column 0, or
the end of the file):

- found: the tokens before it are junk; one error (`expected `)`, found …`) and they are skipped;
- not found: the delimiter is missing. One error, *unclosed delimiter* (E0005), at the insertion point (the
  end of the last token), with a secondary label on the opening delimiter and a machine-applicable
  suggestion inserting it, so `hugin fix` repairs it. Parsing continues as if it were there.

A module body `{ … }` whose items are indented ends, if it is not closed, before the first item in
column 0 (the indentation shows the intended extent), which keeps the rest of the file outside it.

### 4.4 Line heuristic

An argument cannot start in column 0 (reference: lexical-structure, items). The parser uses the same
fact for recovery: a token in column 0 at the start of a line that can start an item ends the item being
parsed, *without discarding what parsed*: a missing period is inserted (E0001 with a machine-applicable
fix and a label "next item starts here"), and an unclosed bracket is reported on its opener. Valid
programs are not affected: the heuristic only applies where the parser would otherwise report an error.

### 4.5 Fuel

Each look at a token costs fuel and consuming one restores it. A loop that does not make progress runs
out of fuel and throws an internal error, which the fuzz tests would find. This turns the classic
recovery bug (an infinite loop on malformed input) into a loud failure.

## 5. Error nodes in later phases

The elaborator does not elaborate an item that contains an error node (or a malformed parameter). The
item is dropped *silently* — its syntax error is the one diagnostic — and the names it declares are
*erroneous*: uses of them in other items are not reported (no E0101), and the items using them are dropped
silently as well, as for items dropped for an elaboration error. Members of a module body are handled one
by one, so a broken member does not take the module with it. The fact loader skips facts with error
nodes. The tree still has the parts that parsed, so document symbols, folding, and completion of the
item's variables work for it.

Considered and rejected: elaborating partially (an error node as a term of unknown type, the item kept).
The elaborator's unit of error recovery is the item (an item with an error is undone as a transaction),
and an item with a hole in it is not meaningful to stage, type at the object level or evaluate; every
later phase would need to know about holes. Keeping the item boundary as the unit, with erroneous names,
gives "no cascading errors" with a change in one place.

## 6. Messages

Every syntax error says what was expected, rendered as a short list of *descriptions*, not a token
dump ("expected `.`, `,` or `:-`", "expected a type", "expected a label"), and what was found. Errors
inside an item carry a secondary label at the start of the construct ("this rule starts here") when the
construct starts on an earlier line. Unclosed delimiters carry a label on the opener. Specific messages
replace the generic one for common mistakes:

| mistake | message | suggestion |
|---|---|---|
| missing `.` before the next item | expected `.`, found `…` + "next item starts here" | insert `.` (machine-applicable) |
| missing `)` `]` `}` | unclosed `(` (E0005) + label on the opener | insert the delimiter (machine-applicable) |
| lowercase parameter `q x : …` | malformed parameter (E0004): a parameter is a variable | `X` (maybe incorrect) |
| lowercase variable after `as` / before `with` | expected a variable, found name `v` | `V` (maybe incorrect) |
| `::` (Haskell) or `:=` in a declaration header | declarations are written `name : type.`, definitions `name = e.` | `:` / `=` (machine-applicable) |
| `=` in a record type, `:` in a record value | record types use `:`, record values `=` | replace (maybe incorrect) |
| `$` not followed by an expression | expected an expression after `$` | — |
| `}` without an open module body | unmatched `}` | — |

Holes outside quoted syntax are a matter of elaboration (E0917), not of syntax: `$x` is also an explicit
splice, valid wherever the meta level allows one.

## 7. Testing

- `tests/recovery/*.hgn`: programs with syntax errors and inline `(*~ E0001 *)` annotations. The runner
  checks the diagnostics (exactly the annotated ones: no cascading errors) and that the items around the
  errors are elaborated, by printing the program after `elaborate` into the `.check` file.
- `RecoveryFuzzSuite`: deleting or inserting one token of a valid corpus program yields at most *k* = 3
  diagnostics, does not crash, and every item that does not contain the damaged token still elaborates
  (its names are in scope after elaboration).
- `tests/fix`: the inserted-delimiter and missing-period suggestions repair programs.
- LSP: hover and completion in the healthy items of a file with a syntax error.
