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
| `SyntaxProblems.scala` | 148 | E0001–E0004 (now also E0005, unclosed delimiter) |
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
| `TokenCursor.scala` | the token cursor, fuel, the look-ahead recovery decides by (layout, delimiters ahead, bodies) |
| `QuoteOpeners.scala` | recovery of damaged quote openers (a prime without its `(`), before parsing |
| `ParserBase.scala` | expected sets, error reporting (one error per region), recovery primitives (skipping, closing delimiters, item ends) |
| `ItemSyntax.scala` | programs and items: declarations, definitions, clauses with `where`, edges, rules, queries; declaration heads |
| `ExprSyntax.scala` | expressions: operators, prefix forms, application, selection, primaries, parentheses |
| `RecordSyntax.scala` | braces: record types and values, implicit binders, module bodies |
| `QuoteSyntax.scala` | reflection: quotes `'( … )` (since #76), holes, lists |
| `DirectiveSyntax.scala` | directives, mode items, attached declarations |
| `SyntaxProblems.scala` | the inventory of syntax errors (E0001–E0005) |

The parts are traits over the concrete `ParserBase` class (the cursor is a field, not a set of abstract
hooks), mixed into `final class Parser`. Quoted syntax has its own part (`QuoteSyntax`), and the recovery
primitives (closing a delimiter, ending an item, skipping to a recovery set) are generic. The explicit
quotes `'( … )` of issue #76 use them: the lexer makes `'` a token only before `{` (the `{` stays a token
of its own, so every depth count treats the quote as a brace), the entries are parsed like rules and
queries (`[@n] e [:- b]`, `?- b`) separated by periods, and the quote is closed with `close`, so an
unclosed `'(` is E0005 with the usual insertion suggestion.

## 4. The resilient parser

### 4.1 Error nodes, repairs and damaged items

- `Trees.ErrorTree(parts)` stands for syntax with an error: something missing (no parts, an empty span
  where it should be: `p X :- q X, .`) or a construct that is *damaged* — unclosed, or followed by tokens
  that were skipped — with the trees that parsed in it (`ErrorTree(List(Parens(…)))`). It is reported
  when it is created; the tree around it is complete.
- `Param.Malformed(tree)` is a declaration parameter that is neither `X` nor `(x : τ)`; the declaration
  keeps its name, its other parameters, its type and its definition.
- Items are never discarded for an error inside them: an error at the end of an item damages its last
  part (`ParserBase.endItem`, `ItemSyntax.damagedItem`). A malformed declaration head without a name
  (`1 : rel.`) cannot declare anything; only that declaration is dropped. Tokens that cannot start an item
  are skipped with the rest of their item, with one error; if they follow an item on the same line, that
  item's period may have been the mistake (`go : nat . -> int.`), and it is damaged too (not for a second
  period, which is harmless, and not for `%use` or `%export`, whose argument is complete). Junk skipped
  in a module body or a `where` block damages the body or the clause (a member may have been lost).

A *repair* is a recovery that is certain about the intended text. The item is then complete, reported,
and elaborated as usual (with a machine-applicable suggestion where there is an edit):

| repair | example |
|---|---|
| a missing `.` before the next item, in an item that starts its line | `edge : int -> rel` ⏎ `path : …` |
| `::` for `:` in a declaration | `f :: int -> int.` |
| `:=` (adjacent) for `=` | `x := 5.` |
| a declaration head in parentheses | `(p) : rel.` |
| a rule name on a declaration (the name is ignored) | `@r p : rel.` |
| an empty `where` (ignored) | `f X = X where.` |

Everything else (an inserted `)`, a missing operand, skipped tokens) is a guess about the intended text,
so the item is damaged: the fix suggestion is still offered (`hugin fix` inserts a missing delimiter), but
the item is not elaborated (§5). The example of E0005 shows why: `edge (X Y.` with `)` inserted at the end
is `edge (X Y)`, an application of `X`; elaborating it would report an error the programmer did not make.

### 4.2 Recovery points and regions

Recovery happens at the innermost construct that can continue:

| construct | separator / end | on an unexpected token |
|---|---|---|
| file, module body, `where` block (`ParserBase.parseItems`) | items | skip the rest of the item, up to its period or the next token in column 0; a `{` at the end of its line (which no item starts with) is skipped with its body, to its `}` |
| query, rule body (after `?-`, `:-`) | formula | a token in column 0 is the next item: the formula is missing (`ErrorTree`), as for the operand of `⇑` |
| item (`endItem`) | `.` | insert `.` if the next token starts a line, closes the enclosing body or is the end of the file; otherwise report and skip to the period, a column-0 token (also inside a delimiter opened in the skipped text, unless it closes one), or the `}` of the enclosing body |
| rule heads, rule body, query | `,` `;` | a missing operand is an `ErrorTree`; the next conjunct parses normally |
| argument list | juxtaposition | an argument that is missing is not consumed (the parent decides) |
| `( … )`, `[ … ]`, `{ … }`, `'( … )`, aggregate `{ t \| b }` (`close`) | closing delimiter | see 4.3 |
| record type / value, list, higher-order hole | `,` | an entry without a label ends the entries, and the closing brace recovers |
| declaration | `:` type `<:` `=` | each part is parsed on its own; a broken definition leaves the name and the type in the tree |

At most one error is reported per *region*: after an error, further errors are suppressed until the
parser has resynchronised (`ParserBase.resync`): it starts a new item, consumes a separator of a rule body
or a list (`,` `;`), or skips to a closing delimiter it was waiting for. This is Scala 3's
`lastErrorOffset` rule extended from positions to regions, and the "one error per mistake" principle of
all four designs. Errors that are not about recovery (an integer out of range, `..` in an update) are
always reported. A token of the lexer's errors (an unterminated string) silences its region: the lexer
reported it.

### 4.3 Delimiters

When the parser expects a closing delimiter and finds something else, it looks for the delimiter ahead,
within the current item: over balanced brackets, ignoring closing delimiters of other kinds, stopping at a
token in column 0 other than the delimiter itself (a `}` in column 0 closes a body over several lines), the
end of the file, or a period at depth 0. A period does not stop the search if the delimiter follows it on
its line (`count { X . | p X }`) or if the token after it cannot start an item (`{ a : t ., b : u }`).
In a construct laid out over several lines (its opening delimiter ends its line) no period stops the
search: such a construct ends with its closer, laid out at the start of a line at the indentation of the
line of its opener. There, a closer that more of the construct follows on its line, while the next closer
of its kind at depth 0 is laid out so (`[`⏎`1,`⏎`2 ] 3`⏎`]`), is stray (``stray `]` ``, E0001) and skipped to
the later one; not if an enclosing construct was opened on a line of the same indentation, whose closer
the later one may be (`m = { k = h {`⏎`a = 1 } 2.`⏎`}.` is valid). Likewise a `}` in the middle of an item
of a module body over several lines, which more of the item follows on its line (`same : t } -> rel.`),
is stray if the body's `}` is laid out so later: the rest of the item is skipped. (A body's `}` follows
the period of its last item, so this never applies to valid text.)

- found: the tokens before it are junk; one error (``expected `)`, found …``) and they are skipped;
- not found: the delimiter is missing. One error, *unclosed delimiter* (E0005), at the insertion point (the
  end of the last token), with a secondary label on the opening delimiter and a machine-applicable
  suggestion inserting it. Parsing continues as if it were there; the construct is damaged.

A prime `'` that no `(` follows right away is reported by the lexer, and recovered before parsing
(`QuoteOpeners`): with a space before the `(` (`' (`) or one token between them on its line (`' {(`) it
opens the quote; if the `(` is lost but a `)` closes the quote ahead, before the end of the item, the `(`
is inserted (`' p X :- q X. )`); otherwise the prime is dropped. The quote is then read silently until
the parser resynchronises.

A `(` or `[` at the end of a line that is never closed, before a token in column 0, is a stray: it is
reported as unclosed at once and does not take the next item into its contents.

A module body `{ … }` that is not closed ends at the end of the file if its first member is in column 0
of a line of its own (the layout of the file then gives no hint), and otherwise before the first item in
column 0. The body is damaged.

### 4.4 Line heuristic

An argument cannot start in column 0 (reference: lexical-structure, items). The parser uses the same
fact for recovery: a token in column 0 at the start of a line ends the item being parsed *without
discarding what parsed*: a missing period is inserted (E0001 with a machine-applicable fix and a label
"next item starts here"), an unclosed bracket is reported on its opener, and skipping stops there. The
operand of `$` and `⇑` cannot start in column 0 either (the one change to the accepted language besides
`(e).l`: no program wrote one there; `$` at the end of a line is a stray), and neither does a user-defined
infix operator continue an expression there (it starts the next item, such as its declaration `op : …`).
Otherwise valid programs are not affected: the heuristic only applies where the parser would otherwise report an error.

An item whose period was inserted is trusted (a repair) only if it starts its line: an item that starts
after other text on its line (`a : rel. b` ⏎) is likely a stray piece of text and is damaged.

### 4.5 Fuel

Each look at the current token's kind costs fuel and consuming a token restores it (1024 looks). A loop
that does not make progress runs out of fuel and throws an internal error, which the fuzz tests and the
"every prefix parses" unit test would find. This turns the classic recovery bug (an infinite loop on
malformed input) into a loud failure. No such failure occurred in the fuzz runs.

## 5. Error nodes in later phases

The elaborator does not elaborate an item that contains an error node or a malformed parameter
(`TreeOps.hasSyntaxErrors`, checked in `Items.elabItem` and for module members): the item is dropped
*silently* — its syntax error is the one diagnostic — and the names it might declare are *erroneous*: the
name of a declaration or definition, and the head names of a rule or clause (a declaration whose `:` is
missing is a rule). Uses of erroneous names are not reported (no E0101); the items using them are dropped
silently, as for items dropped for an elaboration error. In detail:

- items with syntax errors go with the declarations (`splitItems`), which record their names first;
- a function with a clause with a syntax error is declared but not defined (*unelaborated*): its uses
  are dropped silently; so is a function whose clauses fail silently for an erroneous name;
- a module body with a broken member makes the whole item erroneous: its type would lack the member,
  and selections of it elsewhere would fail (E0906);
- erroneous names are silent in quoted syntax (instead of E0917), as directives (instead of an unknown
  directive) and as the declarations of clauses;
- the fact loader skips facts with syntax errors.

The tree still has the parts that parsed, so document symbols list the item, and completion of the
item's variables (which works on tokens) is unaffected. Hover and navigation need elaboration and are not
available inside the broken item; they are in every other item (LSP test in `LanguageServerSuite`).

Considered and rejected: elaborating partially (an error node as a term of unknown type, the item kept).
The elaborator's unit of error recovery is the item (an item with an error is undone as a transaction),
and an item with a hole in it is not meaningful to stage, type at the object level or evaluate; every
later phase would need to know about holes. Keeping the item boundary as the unit, with erroneous names,
gives "no cascading errors" with changes in a few places.

Not covered: the object-level phases report errors about items that depend on a *dropped* item in ways
other than by name — a rule that is not range-restricted because the `%demand` directive that would have
transformed it was dropped, `%derivations @r` for a rule that was dropped. They are the same for an item
dropped for any elaboration error, and predate #53.

## 6. Messages

Every syntax error says what was expected, rendered as a short list of *descriptions*, not a token
dump (``expected `.`, `,` or `:-` ``, "expected a type", "expected a label", "expected an integer"), and
what was found. Errors inside an item carry a secondary label at the start of the construct ("this rule
starts here") when the construct starts on an earlier line. A missing period names the construct
("expected `.` after the declaration"; a rule without body is a "fact"). Unclosed delimiters carry a
label on the opener. Specific messages replace the generic one for common mistakes:

| mistake | message | suggestion |
|---|---|---|
| missing `.` before the next item | ``expected `.` after the rule, found `p` `` + "next item starts here" | insert `.` (machine-applicable) |
| missing `)` `]` `}` | ``unclosed `(` `` (E0005) + label on the opener | insert the delimiter (machine-applicable) |
| lowercase parameter `q x : …` | malformed parameter (E0004): a parameter is a variable | `X` (maybe incorrect) |
| lowercase variable after `as` / before `with` | ``expected a variable, found `v` `` | `V` (maybe incorrect) |
| a token between `as` and its variable (`as { P`) | ``expected a variable, found `{` ``; both skipped, the pattern damaged | — |
| `::` in a declaration header | ``expected `:` in a declaration, found `::` ``; `::` is the list constructor | `:` (machine-applicable) |
| `:=` in a definition header | expected a type, found `=`; a definition without a type is `name = expr.` | remove `:` (machine-applicable) |
| `=` in a record type, `:` in a record value | ``expected `:`, found `=` ``: record types use `:`, record values `=` | replace (maybe incorrect) |
| `$` not followed by an expression | expected an expression; how holes and splices are written | — |
| `:-` in parentheses or a list (the rule form of old) | a rule outside a quote; written `'( h :- b )` (#76) | — |
| `}` without an open module body | unmatched `}` | — |
| a broken list of names in `%use m (x, y).` | the error; the `%use` is damaged as one without a list (it might have opened any name) | — |
| a token before the name of a declaration (`X sel : τ.`) | malformed declaration head (E0004); the declaration keeps the name after it, damaged | — |
| `{` or `[` before a `,` (no braces or list start with one) | ``expected a label, an item or `}` `` (for `{`) or ``expected an expression`` (for `[`), ``found `,` ``; the opener is skipped, the rest belongs to the enclosing construct | — |
| `]` in a list over several lines that goes on after it | ``stray `]` `` + "the construct goes on after this `]`" | — |
| `%infix` with a missing part | expected `left`, `right` or `none` / a precedence (an integer) / the name of the operator | — |

Holes outside quotes are a matter of elaboration (E0917), not of syntax: `$x` is also an explicit
splice, valid wherever the meta level allows one, and the elaborator knows whether a tree is inside a
quote. A lowercase variable at the meta level is in general a
name (a constructor pattern `f x = …` is a clause), so it is detected only where the grammar requires a
variable.

## 7. Testing

- `tests/recovery/*.hgn` (15 programs): syntax errors with inline `(*~ E0001 *)` annotations. The runner
  in `GoldenTests` requires the annotations to account for exactly the diagnostics reported (an error that
  follows from a syntax error fails it) and records the diagnostics and the program after `elaborate` in
  the `.check` file, which shows the items around the errors elaborated (and other errors in them, such
  as an unresolved name, still reported).
- `RecoveryFuzzSuite`: deleting or inserting one token of a valid corpus program (`tests/run`,
  `tests/pos`, `examples`), where that gives a syntax error: no crash; at most *k* = 2 syntax errors; no
  unresolved name outside the damaged line (except the uses of a declaration whose name the mutation
  destroyed); the items from the first one in column 0 after the damaged line parsed unchanged (unless a
  comment or module body was opened and never closed). A damaged `%infix` is excluded (its operator is
  unknown, which changes how the whole file is parsed). 12 seeds × 300 mutants pass; the property found
  the heuristics of §4.1–4.4 that concern stray tokens.
- `ParserSuite`: error nodes, kept declarations, unclosed and skipped delimiters, inserted periods,
  expected sets and construct labels, the specific messages, regions, module body layout, `(e).l`, and
  every prefix of a program parses (no fuel exhaustion).
- `tests/fix`: inserted delimiters and the `::` / `:=` repairs.
- LSP (`LanguageServerSuite`): one diagnostic per mistake, the quick fix of a missing period, hover,
  definition, completion and document symbols in a file with three syntax errors.
