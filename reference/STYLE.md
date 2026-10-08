# Style guide of the Hugin reference

This guide governs every page under `reference/src` (issue #63). It is not part of the book. Its models
are the [Lean Language Reference](https://lean-lang.org/doc/reference/latest/) for prose and examples, and
the [Rust Reference](https://doc.rust-lang.org/reference/) for terse normative statements and grammar
next to prose.

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

## 2. Voice and sentences

- Write in the normative present: "A rule is ...", "It is an error if ...". Use *must* for a
  requirement on programs and *error* for its violation (see "Notation", which defines both words).
- Use simple English, short sentences and the active voice. One sentence states one fact.
- State exact rules exactly. Do not write "generally", "typically", "usually", "in most cases" or
  "basically" when the rule has no exception. If there is an exception, state it.
- Define every term before its first use, in italics at the point of definition (`*stratum*`), and use
  it with exactly that meaning afterwards. Every term is in the glossary of `notation.md`, which fixes
  one word per concept. Do not vary terms for elegance.
- Name things after what they are in this reference, not after the implementation (`Termination.scala`,
  `Tm.Obj`) or a phase of the redesign (B3c, C2).

## 3. Structure of a section

A section that introduces a construct has these parts, in this order, each only if it has content:

1. **Definition**: one or two sentences saying what the construct is.
2. **Syntax**: the grammar productions (EBNF, see `notation.md`) in a ` ```text ` block, next to the
   prose that explains them.
3. **Static rules**: what makes a program that uses the construct valid, with the error codes,
   e.g. "It is an error ([E0605](../errors/E0605.md)) if a bound column is not the last column."
4. **Semantics**: what the construct means when the program is evaluated.
5. **Examples**: small, complete programs (section 4).
6. **Notes**: remarks, in quoted blocks (section 1).

A heading introduces a part that a reader would look up on its own. Do not add a heading for every two
sentences. A page does not end with a summary of itself.

## 4. Examples

- Every example is a complete program. There are no hidden lines.
- One sentence before each example says what it demonstrates: "The following program derives the
  transitive closure of `edge`." Not "Here is an example."
- Use a domain that means something: graphs, family trees, type checking, prices, lists. Do not use
  `foo`, `bar` or `p`/`q` unless the example is about names.
- Keep examples small: one point per example, about 3 to 15 lines.
- Use the block attributes of the test suite (`reference/README.md`); CI checks them:
  - ` ```hugin ` compiles without errors;
  - ` ```hugin,run ` followed by ` ```output ` runs and prints exactly that output (a ` ```facts `
    block between them is the input);
  - ` ```hugin,compile_fail,E0603 ` reports `E0603` as its first error; such an example has one error;
  - ` ```hugin,ignore ` is not checked: use it only for fragments and schemata, never for a program
    that should work.
- An example compiles without warnings, unless it demonstrates the warning.
- Show the output of an example whenever the output is the point.

## 5. Typography and links

- Code, names of the program, keywords, operators and file names are in backticks.
- Metavariables of the grammar and of the rules are italic: *t*, *τ*, *x̄*.
- Bold is used only for the labels of remark blocks and nowhere else.
- Use an em-dash only where no comma, colon or parenthesis works; in practice, not at all. Do not nest
  parentheses in prose, and use at most one parenthetical per sentence.
- Use a list only for items that are parallel and stand alone (cases of a rule, conditions). Explain a
  rule in a paragraph.
- Link the first mention of a term defined on another page, and every error code, with a path relative
  to the page: `[E0603](../errors/E0603.md)` from `object/`, `[E0603](errors/E0603.md)` from the top
  level.
- Cite papers with the short keys of the references list in `notation.md`, e.g. "(Kaminski et al.
  2017)", and link the full entry on first use in a page.

## 6. Words and phrases not to use

Text that reads as generated or as advertising is not allowed. Before a commit, search the pages for
the following and rewrite every hit.

- Openers and closers: "Let's", "In this section we will", "In summary", "To summarize", "Overall",
  "It's worth noting", "Note that" (use a Note block or state the fact), "Importantly", "Crucially",
  "Simply", "Of course".
- Contrast frames: "It's not just X, it's Y", "X isn't merely Y; it's Z", "Rather than X, Hugin Y".
  State what Hugin does.
- Rhetorical questions.
- Triplets for rhythm: "fast, robust, and elegant".
- Marketing words: seamless, powerful, robust, elegant, effortless, leverage, empower, unlock,
  cutting-edge, best-in-class.
- Hedges where the rule is exact: generally, typically, usually, in most cases, basically, essentially.

A check that finds most of them:

```sh
grep -rniE "let's|in this section|in summary|overall,|worth noting|note that|importantly|crucially|simply|seamless|powerful|robust|elegant|effortless|leverage|empower|unlock|generally|typically|usually|in most cases|basically|essentially|—|\?$" reference/src --include=*.md
```

## 7. Good and bad, from our own documents

The following passages are from `README.md` and `docs/`. Each is followed by the form the reference
uses.

**Stacked parentheses and dashes** (`docs/NOTES.md`, soundness of descent):

> There are finitely many facts of each depth: by induction, a fact of depth `k + 1` is derived by a rule
> whose body valuation is determined by its positive atoms (range restriction) — premises of depth `≤ k`
> (finitely many) and facts of earlier components (finitely many) — and arithmetic, equations and
> aggregates are functions of that valuation.

Better: "There are finitely many facts of each depth. The proof is by induction on the depth. A fact of
depth *k* + 1 is derived by a rule whose positive atoms determine its valuation. Those atoms match
premises of depth at most *k* and facts of earlier components, and there are finitely many of both.
Arithmetic, equations and aggregates are functions of the valuation."

**History in a rule** (`docs/REDESIGN.md`, §1.1):

> Every complication of the last months follows from this triangle: probes (values that are interned but
> not asserted), absent terms in comparisons, the two-tier store, E0504, ...

Better: state the rule ("Every constructor is a fact constructor."), and put the reason in a History
block: "> **History.** Before the redesign, constructors were values by default, and `%mode` changed the
answers of programs that observed them."

**Several words for one concept** (`docs/REDESIGN.md`, glossary, and `docs/NOTES.md`):

> **Fact constructor**: a constructor whose terms are facts with Skolem identity (after the redesign:
> every constructor).

The design notes say "constructor", "fact constructor", "data constructor" and "Skolem term"; demand
relations are `r^d`, `r^d[m]`, "the `.check` relation" and "the demand". The reference says
*constructor* (every constructor builds facts) and *demand relation* (`r.check`), and nothing else.

**Evaluation instead of a statement** (`docs/DIAGNOSTICS.md`, survey):

> The `%select` language is powerful but cryptic.

Better: say what the language can and cannot do. "A `%select` pattern chooses a message by the value of
an argument. Its syntax is not documented outside the compiler."

**Hedging and filler** (`docs/NOTES.md`, data and fact constructors):

> A data term in a comparison is simply built (hash-consed, which has no observable effect).

Better: "Evaluating a comparison does not add facts."

## 8. Before committing a page

1. Every example passes `sbt "testOnly hugin.reference.*"`.
2. `mdbook build reference` succeeds and `lychee --offline --include-fragments` finds no broken link.
3. The search of section 6 finds nothing that is not deliberate (a quoted bad example, an operator).
4. Every new term is in the glossary; every page is in `SUMMARY.md`.
5. The rules agree with the implementation. Where the design notes disagree with the implementation,
   the implementation is described, and the difference is recorded in `reference/DISCREPANCIES.md`.
