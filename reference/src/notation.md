# Notation

This chapter fixes the conventions of the reference: the meaning of its normative words, the grammar
notation, the typographic conventions, the terms of the glossary and the works it cites.

## Normative words

A program *must* satisfy a rule, or it is not a valid Hugin program. The implementation rejects it with a
diagnostic whose code starts with `E` (an *error*). "It is an error if ..." states such a rule. The code of
the error is given with the rule and links to its page in the [error index](errors/index.md).

A program *may* do what a rule permits. A *warning* is a diagnostic whose code starts with `W`. A
warning does not make a program invalid; it reports a construct that is valid but probably not what was
meant. Every warning is a *lint* with a name, and its level can be changed on the command line.

Text in a quoted block that starts with **Note**, **Rationale**, **History** or **Limitation** is not
normative. A Limitation names a meaningful program that a rule rejects.

## Grammar notation

The syntax is given by productions in an EBNF notation, in `text` blocks:

```text
Rule      ::= RULE_NAME? Head ("," Head)* (":-" Formula)? "."
```

| notation | meaning |
|---|---|
| `Name ::= ...` | a production of the nonterminal `Name` (nonterminals are capitalised) |
| `"text"` | the token with this text |
| `NAME`, `VAR`, ... | a token class of the [lexical structure](lexical-structure.md) (upper case) |
| `A B` | `A` followed by `B` |
| `A \| B` | `A` or `B` |
| `A?` | `A` or nothing |
| `A*`, `A+` | zero or more, one or more repetitions of `A` |
| `( ... )` | grouping |

Productions describe the text that the parser accepts. Some productions accept more than the language
allows; the static rules in the prose then say which forms are valid. Operator precedence is given by a
table in [Expressions and operators](lexical-structure.md#operators-and-precedence), not by the
productions.

## Typographic conventions

Hugin source text, names declared by programs, keywords and file names are written in `monospace`.
Metavariables, which stand for a piece of syntax in a rule, are in italics: *t* is a term, *τ* a type,
*φ* a formula, *x̄* a sequence *x*₁ … *x*ₙ. A term in italics at its first occurrence is being defined;
the glossary below lists it.

Examples are complete programs. An example followed by an `output` block prints exactly that output
when it is run with `hugin run`; an example followed by a `facts` block reads those facts as its input.
The continuous integration of the implementation compiles and runs every example of this reference.

## Glossary

Each concept has one name in this reference. The glossary gives that name, a short definition and the
section that defines it.

| term | definition | defined in |
|---|---|---|
| aggregate | a formula `X = k { t \| φ }` that binds `X` to the count, sum, minimum or maximum of `t` over the solutions of `φ` | [Aggregates](object/aggregates.md) |
| anchor | the finite set in which guarded induction keeps the measure of a head | [Termination](object/termination.md#guarded-induction-b) |
| answer | a valuation of the variables of a query under which its formula holds | [Queries and output](object/io.md#queries) |
| atom | a formula `r t̄` that holds if `r t̄` is a fact | [Rules](object/rules.md#formulas) |
| attribute | what a local directive attaches to a declaration, such as `ainput` for `%input` | [Directives](directives.md#local-directives) |
| base type | `int`, `float` or `string` | [Object types](object/types.md#base-types) |
| body | the formula after `:-` of a rule | [Rules](object/rules.md) |
| bound column | the last column of a relation, declared `min τ` or `max τ`, of which a relation keeps only the best value per key | [Bound columns](object/bound-columns.md) |
| clause | an equation `f p̄ = e.` that defines a meta function for the arguments that match the patterns `p̄` | [Clauses](meta/clauses.md) |
| column | a parameter position of a relation or constructor, with a type and an optional label | [Declarations](object/declarations.md) |
| component | a strongly connected component of the dependency graph; the unit of evaluation | [Evaluation](object/index.md#evaluation) |
| constant | a name declared by a declaration: an object constant or a meta constant | [Declarations](object/declarations.md) |
| constructor | an object constant `c : τ̄ -> a` whose result is an object type; its terms are facts | [Facts and identity](object/facts.md) |
| coverage | the property that the clauses of a function match every argument | [Coverage](meta/coverage.md) |
| demand relation | the relation `r.check` that `%demand` declares for `r`; it holds the inputs for which `r` is computed | [Directives](directives.md#demand) |
| derived constant | an object constant `r.l` named after another constant `r` by the primitive `derive` | [Reflection](reflection.md#symbols-and-derived-constants) |
| descent (A) | the termination argument by which every cycle of derivation steps makes an argument smaller | [Termination](object/termination.md#descent-along-derivations-a) |
| directive | an item `%d a₁ … aₙ.` that applies the meta function `d` to change the program | [Directives](directives.md) |
| fact | a ground atom that holds in the database; it has an identity | [Facts and identity](object/facts.md) |
| family | a declaration with type parameters (`list A : type.`); its applications to object types are instances | [Families](object/types.md#families) |
| footprint | the part of the program a directive changes, read off its type: local, additive or module-wide | [Directives](directives.md#footprints) |
| formula | a condition of a rule body or query: atoms, comparisons, negations, aggregates, conjunctions, disjunctions | [Rules](object/rules.md#formulas) |
| formula function | a meta function whose result is a formula, of type `… -> prop` | [Staging](meta/staging.md#formula-functions) |
| functor | a meta function that returns a module | [Modules](modules.md#functors) |
| guarded induction (B) | the termination argument by which a measure decreases along every recursive call and stays in a finite set | [Termination](object/termination.md#guarded-induction-b) |
| head | an atom before `:-` of a rule; the fact the rule derives | [Rules](object/rules.md) |
| hole | `$X`, `$..Xs` or `$F[V]` inside a quote: a place for a meta value | [Reflection](reflection.md#holes) |
| identity | the value that stands for a fact; two facts with the same relation and arguments have the same identity | [Facts and identity](object/facts.md#identity) |
| implicit argument | an argument the elaborator infers, for a binder `{x : A}` | [Functions](meta/functions.md#implicit-arguments) |
| inductive family | a meta type `T : Δ -> Type` defined by its meta constructors | [Inductive families](meta/families.md) |
| input relation | a relation declared `%input` or `%open`, whose facts may come from a facts file | [Queries and output](object/io.md#input-facts) |
| instance | the object constants of a family or module body at particular arguments | [Families](object/types.md#families), [Modules](modules.md) |
| item | a top-level unit of a file, ended by `.`: a declaration, definition, clause, rule, query or directive | [Lexical structure](lexical-structure.md#items) |
| key | the columns of a bound relation other than its bound column | [Bound columns](object/bound-columns.md) |
| label | the name `l` of a column declared `(l : τ)` | [Declarations](object/declarations.md#columns-and-labels) |
| level | the index *i* of a universe `Typeᵢ` | [Universes](meta/universes.md) |
| measure | a tuple of argument positions that guarded induction orders | [Termination](object/termination.md#guarded-induction-b) |
| meta constant | a constant whose type is a meta type: a function, definition, inductive family, meta constructor or postulate | [The meta level](meta/index.md) |
| meta constructor | a constructor of an inductive family | [Inductive families](meta/families.md) |
| meta function | a meta constant of a Π type, defined by clauses or by a definition | [Functions](meta/functions.md) |
| meta level | the compile-time language: a total, dependently typed functional language (stage 1) | [The meta level](meta/index.md) |
| module | a record value whose fields are the constants of a module body or of a file | [Modules](modules.md) |
| object code | a term of the object level as a meta value: a term, formula, relation or item to be staged | [Staging](meta/staging.md) |
| object constant | an object type, constructor or relation | [Declarations](object/declarations.md) |
| object level | the evaluated language: Datalog∃! (stage 0) | [The object level](object/index.md) |
| object type | a type of object values, of the universe `type` | [Object types](object/types.md) |
| object variable | an uppercase variable of a rule or query | [Rules](object/rules.md#variables) |
| open type | an object type `a : type.` whose members are the constructors and relations declared into it | [Object types](object/types.md#open-types) |
| pattern | the left side of a clause, matched against arguments | [Clauses](meta/clauses.md#patterns) |
| prelude | the library included in every program | [The prelude](prelude.md) |
| quote | `'{ … }`: object syntax as reflective data, of the category the expected type gives | [Reflection](reflection.md#quotes) |
| quoted pattern | a quote used as a pattern over reflective data, with holes | [Reflection](reflection.md#quoted-patterns) |
| range restriction | the rule that every variable of a rule is bound by its body | [Rules](object/rules.md#range-restriction) |
| reflect | turn reflective data into object items of the program | [Reflection](reflection.md#reflecting-data-into-the-program) |
| reflective type | one of the prelude types `term`, `formula`, `rule`, `item`, `module` (and `sym`, `decl`, `measure`) that represent object syntax as data | [Reflection](reflection.md) |
| reify | turn object syntax into reflective data, by a quote | [Reflection](reflection.md#quotes) |
| relation | an object constant `r : τ̄ -> rel`; a set of facts | [Declarations](object/declarations.md) |
| rule | an item `h̄ :- φ.` that derives the heads `h̄` for every valuation that satisfies `φ` | [Rules](object/rules.md) |
| signature | a record type used as the type of modules | [Modules](modules.md#signatures) |
| splice | `$e`: meta code that computes object code, inserted into object code | [Staging](meta/staging.md) |
| stage | 0 for the object level, 1 for the meta level | [Staging](meta/staging.md) |
| stratum | a set of components evaluated after all relations it negates or aggregates over | [Negation](object/negation.md) |
| symbol | a meta value of type `sym` that refers to an object constant | [Reflection](reflection.md#symbols-and-derived-constants) |
| universe | `type`, the type of object types, or `Typeᵢ`, a type of meta types | [Universes](meta/universes.md) |
| valuation | an assignment of values to the variables of a rule or query | [Rules](object/rules.md#semantics) |
| value | a literal or an identity | [Facts and identity](object/facts.md#values) |
| value invention | a rule that can derive a value that did not exist before: a new constructor term or an arithmetic result | [Termination](object/termination.md#value-invention) |

## References

The reference cites the following works by the keys in the first column.

| key | work |
|---|---|
| Gilray et al. 2024 | T. Gilray, A. Sahebolamri, Y. Sun, S. Kunapaneni, S. Kumar, K. Micinski. *Datalog with First-Class Facts.* arXiv:2411.14330, 2024. The language DL∃! with Skolem identity of facts, on which the object level is based. |
| Hugin definition | *Hugin: A Two-Level Typed Datalog with First-Class Facts. Formal Language Definition*, draft revision 7. The definition of the language before the redesign; section numbers of the form "Section 6.4" in diagnostics refer to it. |
| Kovács 2022 | A. Kovács. *Staged Compilation with Two-Level Type Theory.* ICFP 2022. Stage inference and the two-level type theory of the meta level. |
| Annenkov et al. 2023 | D. Annenkov, P. Capriotti, N. Kraus, C. Sattler. *Two-Level Type Theory and Applications.* Mathematical Structures in Computer Science, 2023. |
| Kaminski et al. 2017 | M. Kaminski, B. Cuenca Grau, E. Kostylev, B. Motik, I. Horrocks. *Foundations of Declarative Data Analysis Using Limit Datalog Programs.* IJCAI 2017 (arXiv:1705.06927). Limit Datalog, the source of bound columns. |
| Berent et al. 2022 | L. Berent, M. Nissl, E. Sallinger. *Complexity of Arithmetic in Warded Datalog±.* arXiv:2202.05086, 2022. Type-consistency (Definition 4). |
| Lee et al. 2001 | C. S. Lee, N. D. Jones, A. M. Ben-Amram. *The Size-Change Principle for Program Termination.* POPL 2001. |
| Cockx and Abel 2018 | J. Cockx, A. Abel. *Elaborating Dependent (Co)pattern Matching.* ICFP 2018. Case trees and index unification for clauses. |
| Stucki et al. 2018 | N. Stucki, A. Biboudis, M. Odersky. *A Practical Unification of Multi-stage Programming and Macros.* GPCE 2018. Quoted patterns with holes. |
