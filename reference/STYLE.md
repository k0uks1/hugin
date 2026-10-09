# Style guide of the Hugin reference

This guide governs every page under `reference/src`, the error explanations in `docs/errors` and the
`README.md` (issue #63). It is not part of the book. Its models are the
[Lean Language Reference](https://lean-lang.org/doc/reference/latest/) for prose and examples, and the
[Rust Reference](https://doc.rust-lang.org/reference/) for terse normative statements and grammar next
to prose. Section 2 records what we took from each, read from their sources
([leanprover/reference-manual](https://github.com/leanprover/reference-manual),
[rust-lang/reference](https://github.com/rust-lang/reference)).

## 1. What the reference is

The reference defines the language that the implementation accepts. A statement in it is either
*normative* (a rule of the language) or a *remark* (motivation, history, a hint). Normative text is plain
prose. Remarks are set apart in a quoted block that starts with a bold label:

```markdown
> **Note.** Earlier versions of Hugin had data constructors that were not facts.
```

The labels are **Note** (a remark), **Rationale** (why a rule is as it is), **History** (how it came to
be) and **Limitation** (a program the rule rejects although it is meaningful). Nothing in such a block
is a rule. The design notes under `docs/` are history; the reference cites them only in a History
block.

## 2. What we took from the two models

### From the Lean Language Reference

We read the chapters on inductive types (`Manual/Language/InductiveTypes.lean`), structural recursion
(`Manual/RecursiveDefs/Structural.lean`), definitions (`Manual/Defs.lean`), elaboration
(`Manual/Elaboration.lean`), the error explanations (`Manual/ErrorExplanations/`), its contributor guide
and its Vale rules (`.vale/styles/Lean`).

- **A chapter opens with a definition.** The first sentence names the subject in italics and says what
  it is: "_Inductive types_ are the primary means of introducing new types to Lean." The next sentences
  say what it consists of and what follows from it. Only then comes the first heading. Ours: "A *rule*
  derives facts from facts. It has one or more *heads*, which are atoms, and an optional *body*, which is
  a formula."
- **A term is defined once and then used with exactly that meaning.** Lean marks the definition
  (`deftech`) and links every use (`tech`), and its Vale rule `TechnicalTerms.yml` replaces variant
  spellings ("typeclass" by "type class"). Ours: the glossary of `notation.md` and its table of terms
  not used, checked by `scripts/check-style.sh`.
- **Examples are set apart from the description.** Each Lean example has a title that says what it
  shows ("A constructorless type", "Structural Recursion vs Subtraction"). The output follows the code
  directly (`leanOutput`), and a failing example shows its message. Prose after the output explains the
  result only where it is not obvious ("This is because there was no pattern matching on the parameter
  `n`."). Ours: one sentence before the example says what it demonstrates, the `output` block follows,
  and an explanation follows only if it adds something.
- **An error explanation says when the error is raised, then shows it.** Lean's explanations open with
  one paragraph ("In an inductive declaration, the resulting type of each constructor must match the
  type being declared; if it does not, this error is raised.") and give examples as triples: the broken
  code, the message and the fixed code, with a sentence on what the fix changes. Ours: section 5.
- **Lists are introduced by a complete sentence ending in a colon,** and their items are either all
  complete sentences or all fragments.
- **Every empirical claim is tested,** by an example or a hidden test. Ours: every claim about what a
  program prints is a `hugin,run` example.

We did not adopt one sentence per source line, title case for headings, or Lean's occasional informal
openers ("Roughly speaking", "Generally speaking"), which section 7 rules out.

### From the Rust Reference

We read `items/functions.md`, `patterns.md`, `expressions/if-expr.md`, `glossary.md`, the conventions in
`introduction.md` and the authoring guide (`dev-guide/src/style.md`, `examples.md`, `rules/index.md`,
`formatting/admonitions.md`, `formatting/markdown.md`).

- **The grammar comes first, then one paragraph per fact.** A Rust section starts with its grammar block,
  then an *intro* paragraph that explains the construct, then paragraphs that each state one rule: "If the
  output type is not explicitly stated, it is the unit type." Ours: the syntax block next to the defining
  paragraph, then one paragraph per rule, each with its error code.
- **Normative sentences are short and in the present tense.** "An `if` expression must have the same
  type in all situations." "Function parameters are irrefutable patterns." Ours: section 3.
- **Notes, examples and warnings are admonitions,** and an admonition never states a rule. Ours: the
  remark blocks of section 1.
- **A failing example is one block per failure, tagged with its error code** (`compile_fail,E0277`);
  success cases may share a block. An `ignore` example needs a reason. Ours: section 4.
- **Wording rules:** sentence-case headings; no slash for alternatives ("program/binary" becomes "program
  or binary"); no "in Rust", since the whole book is about Rust. Ours: no "in Hugin", and no `min int /
  max int`.
- **Links between chapters are relative and end in `.md`,** so the link checker can follow them.

We did not adopt the rule identifiers `r[items.fn.params]`: they need the `mdbook-spec` preprocessor, and
our headings and error codes already give stable anchors. We did not adopt American spelling either; the
reference is written in British spelling with *-ise* (`memoised`, `normalised`, `labelled`), and
identifiers in code keep their own spelling.

## 3. Voice and sentences

- Write in the normative present: "A rule is ...", "It is an error ([E0603](...)) if ...". Use *must*
  for a requirement on programs and *error* for its violation (see "Notation", which defines both words).
- Use simple English, short sentences and the active voice. One sentence states one fact.
- State exact rules exactly. Do not write "generally", "typically", "usually", "in most cases" or
  "basically" when the rule has no exception. If there is an exception, state it.
- Define every term before its first use, in italics at the point of definition (`*stratum*`), and use
  it with exactly that meaning afterwards. Every term is in the glossary of `notation.md`, which fixes
  one word per concept and lists the words that are not used. Do not vary terms for elegance.
- Name things after what they are in this reference, not after the implementation (`Termination.scala`,
  `Tm.Obj`) or a phase of the redesign (B3c, C2). The explanations of retired codes may name the
  redesign step that retired them.
- Do not write "in Hugin": the whole reference is about Hugin.
- Put motivation, history and hints for tools (the language server, `hugin fix`) in a remark block, not
  in the paragraph that states the rule.

## 4. Structure of a section

A section that introduces a construct has these parts, in this order, each only if it has content:

1. **Definition**: one or two sentences saying what the construct is, with its name in italics.
2. **Syntax**: the grammar productions (EBNF, see `notation.md`) in a ` ```text ` block, next to the
   prose that explains them.
3. **Static rules**: what makes a program that uses the construct valid, with the error codes,
   e.g. "It is an error ([E0605](../errors/E0605.md)) if a bound column is not the last column."
4. **Semantics**: what the construct means when the program is evaluated.
5. **Examples**: small, complete programs (see "Examples" below).
6. **Notes**: remarks, in quoted blocks (section 1).

A chapter may say in one sentence what it defines ("This chapter defines ..."). A heading introduces a
part that a reader would look up on its own. Do not add a heading for every two sentences. A page does
not end with a summary of itself.

### Examples

- Every example is a complete program. There are no hidden lines.
- One sentence before each example says what it demonstrates: "The following program derives the
  transitive closure of `edge`." Not "Here is an example." For a failing example, the sentence says why
  it fails: "The following rule is rejected, since nothing binds `Y`."
- Use a domain that means something: graphs, family trees, type checking, prices, orders, games. Do not
  use `foo`, `bar`, `p`/`q`, `w` or `mk` unless the example is about names.
- Keep examples small: one point per example, about 3 to 15 lines.
- Use the block attributes of the test suite (`reference/README.md`); CI checks them:
  - ` ```hugin ` compiles without errors;
  - ` ```hugin,run ` followed by ` ```output ` runs and prints exactly that output (a ` ```facts `
    block between them is the input);
  - ` ```hugin,compile_fail,E0603 ` reports `E0603` as its first error; such an example has one error;
  - ` ```hugin,ignore ` is not checked: use it only for fragments and schemata, never for a program
    that should work, and say in the sentence before it why it is not checked.
- An example compiles without warnings, unless it demonstrates the warning.
- Show the output of an example whenever the output is the point.

## 5. Error explanations

Each file `docs/errors/<code>.md` has this shape. The title line must be `# <code>: <title>` with the
title of the code in `Code.scala`; `ExplanationsSuite` checks it and the examples.

1. One sentence that says when the error is reported: "A name is declared twice in the same scope."
2. `## Example`: a program whose first error is the code (` ```hugin fail=E0102 `), in a meaningful
   domain.
3. `## Why this is an error`: the rule the program breaks, in the words of the reference, then one
   sentence on the example ("Here `X` is a `person` in one atom and a `city` in the other."). Link the
   chapter of the reference with its absolute URL, since `hugin explain` prints the text in a terminal:
   "See [Termination](https://k0uks1.github.io/hugin/object/termination.html)."
4. `## How to fix it`: one sentence that says what the fix changes, ending with a colon ("Give the
   second relation a name of its own:"), then the fixed program.
5. `## Related` (optional): other codes, as `E0002 (unterminated comment or string)`.

An explanation does not cite `docs/NOTES.md` or `docs/REDESIGN.md`. A retired code keeps its old
explanation after the line `**Retired** (redesign step ...)`, which `error-index.py` looks for.

## 6. Typography, links and citations

- Code, names of the program, keywords, operators and file names are in backticks.
- Metavariables of the grammar and of the rules are italic: *t*, *τ*, *x̄*. A *metavariable* is a
  placeholder of the grammar; a variable of a clause is a *pattern variable*.
- Bold is used only for the labels of remark blocks (and of the `**Retired**` line), nowhere else.
- Use an em-dash only where no comma, colon or parenthesis works; in practice, not at all. Do not nest
  parentheses in prose, and use at most one parenthetical per sentence, apart from error codes and links.
- Use a list only for items that are parallel and stand alone (cases of a rule, conditions). Introduce
  it with a complete sentence ending in a colon. Explain a rule in a paragraph.
- Write alternatives with "or", not with a slash.
- Headings are in sentence case.
- Link the first mention of a term defined on another page, and every error code, with a path relative
  to the page: `[E0603](../errors/E0603.md)` from `object/`, `[E0603](errors/E0603.md)` from the top
  level.
- Cite papers by the keys of the references in `notation.md`. A citation is the key in parentheses after
  the statement it supports, with a locator after a comma: "(Lee et al. 2001, Theorem 4)". The first
  citation of a work in a chapter links to the references:
  `([Kaminski et al. 2017](../notation.md#references))`. Do not use the key as a noun ("In terms of
  Gilray et al. 2024, ...").
- Wrap prose at 105 columns. Do not break inline code or a link target across lines.

## 7. Words and phrases not to use

Text that reads as generated or as advertising is not allowed. `scripts/check-style.sh` (run in the CI
job "Formatting") rejects the following in `reference/src` and `docs/errors`, outside code. Rewrite
every hit.

- Openers and closers: "Let's", "In this section we", "In summary", "To summarize", "It's worth noting",
  "Note that" (use a Note block or state the fact), "Importantly", "Crucially", "Of course", "Here is an
  example".
- Contrast frames: "It's not just X, it's Y", "X isn't merely Y". State what Hugin does.
- Rhetorical questions.
- Marketing words: seamless, powerful, robust, elegant, effortless, leverage, empower, unlock,
  cutting-edge, best-in-class, state-of-the-art, "the full power of".
- Hedges where the rule is exact: generally, typically, usually, basically, in most cases.
- Em-dashes.
- The terms that the glossary retires: fact constructor, data constructor, subfact, Skolem term,
  inductive type (outside `notation.md` and the explanations of retired codes).

The script cannot see the following, which review must catch: triplets for rhythm ("fast, robust, and
elegant"), "Rather than X, Hugin Y", "Simply", stacked parentheticals, a summary at the end of a
section, bold in sentences, and two words for one concept that the glossary does not list yet.

## 8. Good and bad, from our own text

Each pair is a passage of the reference or of an error explanation before the editorial pass of issue
#63, and the form it has now.

**A remark in a rule** (`meta/universes.md`):

> It is an error (E0904) if the levels cannot be chosen consistently [...]. `Type : Type` is excluded
> because it would make the meta level inconsistent and its evaluation possibly non-terminating.

Better: the rule alone, and "> **Rationale.** `Type : Type` would make the meta level inconsistent, and
its evaluation could fail to terminate."

**A hedge** (`object/termination.md`):

> The compiler decides this statically, without annotations in the common cases.

Better: "The compiler checks this statically. [...] A program may declare a measure with `%terminates`
where the inferred measures do not suffice."

**Tooling and motivation inside the rule, with a stacked parenthetical** (`meta/functions.md`, typed
holes):

> A hole is written while a program is developed step by step (the language server shows its goal and
> offers to split cases and to add the clauses that are missing, with holes for their right-hand sides).

Better: the rule ("Every hole is an error (E0924), whose diagnostic reports the goal and the variables
in scope."), then "> **Note.** Holes support writing a program step by step. The language server shows
the goal of a hole, and offers to split cases and to add missing clauses."

**Parentheses inside a list item** (`meta/staging.md`):

> a *quote* `⟨t⟩` turns object code `t` into a meta value of type `⇑A` (it is inserted, never written;
> the quotes `'{ … }` of reflection are another construct: they make data of the reflective types, not
> object code);

Better: "a *quote* `⟨t⟩` turns object code `t` into a meta value of type `⇑A`. It is inserted, never
written. The quotes `'{ … }` of reflection are a different construct, which makes data of the reflective
types;"

**"In Hugin" and the citation as a noun** (`object/facts.md`):

> In Hugin facts are first class: [...] This is the logic DL∃! of Gilray et al. 2024.

Better: "Facts are first class: [...] This is the logic DL∃! ([Gilray et al. 2024](../notation.md#references))."

**A retired term and design notes in an explanation** (`docs/errors/E0603.md`):

> A rule asserting a fact-constructor term in its head is also evaluated in that constructor's
> component, so it counts there too (see `docs/NOTES.md`). [...] (`min int` / `max int`)

Better: "A rule that builds a constructor term in its head is also evaluated in the component of the
constructor, so it counts there too. See [Termination](https://k0uks1.github.io/hugin/object/termination.html)."
and "(`min int` or `max int`)".

**Names that mean nothing** (`object/negation.md`):

> The following program is not stratified: `p` and `q` negate each other.

Better: "The following program is not stratified: a position is winning if a move leads to a position
that is not winning, so `win` depends on itself through a negation." with `win X :- move X Y, not win Y.`

**A note that contradicts its example** (`meta/coverage.md`):

> A clause that matches only some of the values its patterns allow is not unreachable. In `isZero zero =
> 1. isZero N = 0. isZero (suc N) = 0.` the third clause is unreachable [...]

Better: "A clause is unreachable only if the clauses before it together match everything it matches.
[...] The second clause is reachable, although the first matches one of its arguments."

**A fix without a sentence** (`docs/errors/E0102.md`): the fixed program followed the heading directly.
Better: "Give the second relation a name of its own:" before it.

The design notes also show what to avoid. `docs/NOTES.md` stacks parentheses and dashes ("whose body
valuation is determined by its positive atoms (range restriction) — premises of depth `≤ k` (finitely
many) and facts of earlier components (finitely many) — and ..."), and `docs/DIAGNOSTICS.md` evaluates
instead of stating ("The `%select` language is powerful but cryptic."). The reference says what a
construct does and what it cannot do.

## 9. Before committing a page

1. Every example passes `sbt "testOnly hugin.reference.*"`; every explanation passes
   `sbt "testOnly hugin.util.diagnostics.ExplanationsSuite"`.
2. `mdbook build reference` succeeds and `lychee --offline --include-fragments` finds no broken link.
3. `scripts/check-style.sh` passes, and the page has none of the problems that section 7 leaves to
   review.
4. Every new term is in the glossary; every page is in `SUMMARY.md`.
5. The rules agree with the implementation. Where the design notes disagree with the implementation,
   the implementation is described, and the difference is recorded in `reference/DISCREPANCIES.md`.
