# Notation

This chapter fixes the conventions of the reference: the meaning of its normative words, the grammar
notation, the typographic conventions, the terms of the glossary and the works it cites.

## Normative words

A program *must* satisfy a rule, or it is not a valid Hugin program. The implementation rejects it with a
diagnostic whose code starts with `E` (an *error*). "It is an error if ..." states such a rule. The code
of the error is given with the rule and links to its page in the [error index](errors/index.md).

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

The design notes and older diagnostics use other words for some of these concepts. The reference does
not use them:

| not used | use |
|---|---|
| fact constructor, data constructor, Skolem term | constructor (every constructor builds facts) |
| subfact | nested fact |
| inductive type, data type (of the meta level) | inductive family |
| meta variable (a variable of meta code) | pattern variable, or variable of meta code; a *metavariable* is a placeholder of the grammar |
| compile-time value | meta value |
| mode, moded relation | demand relation (`%demand`); there are no modes |
| SCC | component |
| predicate | relation |

| term | definition | defined in |
|---|---|---|
| abstract type | an object type that a functor's parameter gives, which in the functor's body is a subtype only of itself | [Object types](object/types.md#functor-bodies) |
| aggregate | a formula `X = k { t \| φ }` that binds `X` to the count, sum, minimum or maximum of `t` over the solutions of `φ` | [Aggregates](object/aggregates.md) |
| anchor | the finite set in which guarded induction keeps the measure of a head | [Termination](object/termination.md#guarded-induction-b) |
| answer | a valuation of the variables of a query under which its formula holds | [Queries and output](object/io.md#queries) |
| ascription | a term `(t : τ)` that states the type of `t`, or tests it as a checked downcast | [Object types](object/types.md#ascriptions) |
| atom | a formula `r t̄` that holds if `r t̄` is a fact | [Rules](object/rules.md#formulas) |
| attribute | what a local directive attaches to a declaration, such as `ainput` for `%input` | [Directives](directives.md#local-directives) |
| base type | `int`, `float` or `string` | [Object types](object/types.md#base-types) |
| body | the formula after `:-` of a rule | [Rules](object/rules.md) |
| bound column | the last column of a relation, declared `min τ` or `max τ`, of which a relation keeps only the best value per key | [Bound columns](object/bound-columns.md) |
| clause | an equation `f p̄ = e.` that defines a meta function for the arguments that match the patterns `p̄` | [Clauses](meta/clauses.md) |
| closed type | a fact type or a union of closed types; projections and updates apply to it | [Object types](object/types.md#unions) |
| column | a parameter position of a relation or constructor, with a type and an optional label | [Declarations](object/declarations.md) |
| component | a strongly connected component of the dependency graph; the unit of evaluation | [Evaluation](object/index.md#evaluation) |
| constant | a name declared by a declaration: an object constant or a meta constant | [Declarations](object/declarations.md) |
| constructive rule | a rule that performs value invention | [Termination](object/termination.md#value-invention) |
| constructor | an object constant `c : τ̄ -> a` whose result is an open type; its terms are facts | [Facts and identity](object/facts.md) |
| coverage | the property that the clauses of a function match every argument | [Coverage](meta/coverage.md) |
| database | the set of facts that a program denotes | [Evaluation](object/index.md#evaluation) |
| demand relation | the relation `r.check` that `%demand` declares for `r`; it holds the inputs for which `r` is computed | [Directives](directives.md#demand) |
| dependency graph | the graph with an edge from `r` to `s` if a rule of `r` reads `s`; an edge under `not` or in an aggregate is negative | [Evaluation](object/index.md#evaluation) |
| derived constant | an object constant `r.l` named after another constant `r` by the primitive `derive` | [Reflection](reflection.md#symbols-and-derived-constants) |
| descent (A) | the termination argument by which every cycle of derivation steps makes an argument smaller | [Termination](object/termination.md#descent-along-derivations-a) |
| directive | an item `%d a₁ … aₙ.` that applies the meta function `d` to change the program | [Directives](directives.md) |
| fact | a ground atom that holds in the database; it has an identity | [Facts and identity](object/facts.md) |
| fact type | the type `c` of a relation, struct or constructor `c`, whose values are the identities of the facts of `c` | [Object types](object/types.md#fact-types) |
| family | a declaration with type parameters (`list A : type.`); its applications to object types are instances | [Families](object/types.md#families) |
| finite source | a positive body atom of a relation outside the component of the rule | [Termination](object/termination.md#value-invention) |
| footprint | the part of the program a directive changes, read off its type: local, additive or module-wide | [Directives](directives.md#footprints) |
| formula | a condition of a rule body or query: atoms, comparisons, negations, aggregates, conjunctions, disjunctions | [Rules](object/rules.md#formulas) |
| formula function | a meta function whose result is a formula, of type `… -> prop` | [Staging](meta/staging.md#formula-functions) |
| functor | a meta function that returns a module | [Modules](modules.md#functors) |
| goal | the type that the position of a typed hole expects | [Functions](meta/functions.md#typed-holes) |
| guard | the atom `r.check t̄ᵢ` that `%demand` adds to the body of every rule of `r`; it bounds the inputs of `r` | [Directives](directives.md#what-demand-generates) |
| guarded induction (B) | the termination argument by which a measure decreases along every recursive call and stays in a finite set | [Termination](object/termination.md#guarded-induction-b) |
| head | an atom before `:-` of a rule; the fact the rule derives | [Rules](object/rules.md) |
| hole | `$X`, `$..Xs` or `$F[V]` inside a quote: a place for a meta value | [Reflection](reflection.md#holes) |
| identity | the value that stands for a fact; two facts with the same relation and arguments have the same identity | [Facts and identity](object/facts.md#identity) |
| implicit argument | an argument the elaborator infers, for a binder `{x : A}` | [Functions](meta/functions.md#implicit-arguments) |
| inductive family | a meta type `T : Δ -> Type` defined by its meta constructors | [Inductive families](meta/families.md) |
| input relation | a relation declared `%input` or `%open`, whose facts may come from a facts file | [Queries and output](object/io.md#input-facts) |
| instance | the object constants of a family or module body at particular arguments | [Families](object/types.md#families), [Modules](modules.md) |
| item | a top-level unit of a file, ended by `.`: a declaration, definition, clause, rule, query or directive | [Lexical structure](lexical-structure.md#items) |
| join | the least common supertype of two types | [Rules](object/rules.md#records) |
| key | the columns of a bound relation other than its bound column | [Bound columns](object/bound-columns.md) |
| label | the name `l` of a column declared `(l : τ)` | [Declarations](object/declarations.md#columns-and-labels) |
| level | the index *i* of a universe `Typeᵢ` | [Universes](meta/universes.md) |
| lifting | the meta function `τ -> ⇑τ⁰` that turns meta values of a base type, object code or a shared data type into object code; stage inference inserts it | [Staging](meta/staging.md#lifting) |
| measure | a tuple of argument positions that guarded induction orders | [Termination](object/termination.md#guarded-induction-b) |
| meet | the greatest common subtype of two types | [Object types](object/types.md#subtyping) |
| member | a constructor, relation or struct whose facts are values of an open type, directly or through an edge between open types | [Object types](object/types.md#open-types) |
| meta constant | a constant whose type is a meta type: a function, definition, inductive family, meta constructor or postulate | [The meta level](meta/index.md) |
| meta constructor | a constructor of an inductive family | [Inductive families](meta/families.md) |
| meta function | a meta constant of a Π type, defined by clauses or by a definition | [Functions](meta/functions.md) |
| meta level | the compile-time language: a total, dependently typed functional language (stage 1) | [The meta level](meta/index.md) |
| meta value | a value of a meta type, computed at compile time | [Functions](meta/functions.md#literals-and-primitive-operations) |
| module | a record value whose fields are the constants of a module body or of a file | [Modules](modules.md) |
| nested fact | a fact that occurs as a subterm of another fact; deriving or loading a fact adds its nested facts | [Facts and identity](object/facts.md#constructor-terms-in-heads) |
| object code | a term of the object level as a meta value: a term, formula, relation or item to be staged | [Staging](meta/staging.md) |
| object constant | an object type, constructor or relation | [Declarations](object/declarations.md) |
| object level | the evaluated language: Datalog∃! (stage 0) | [The object level](object/index.md) |
| object type | a type of object values, of the universe `type` | [Object types](object/types.md) |
| object variable | an uppercase variable of a rule or query | [Rules](object/rules.md#variables) |
| open type | an object type `a : type.` whose members are the constructors and relations declared into it | [Object types](object/types.md#open-types) |
| pattern | the left side of a clause, matched against arguments | [Clauses](meta/clauses.md#patterns) |
| postulate | a meta constant with a type and no value | [The meta level](meta/index.md#meta-items) |
| prelude | the library included in every program | [The prelude](prelude.md) |
| query | an item `?- φ.` that asks for the answers of `φ` | [Queries and output](object/io.md#queries) |
| quote | `'{ … }`: object syntax as reflective data, of the category the expected type gives | [Reflection](reflection.md#quotes) |
| quoted pattern | a quote used as a pattern over reflective data, with holes | [Reflection](reflection.md#quoted-patterns) |
| quoted term | a value of `quoted A`: `term` data that describes a term of the object type `A` | [Reflection](reflection.md#typed-terms) |
| range restriction | the rule that every variable of a rule is bound by its body | [Rules](object/rules.md#range-restriction) |
| refinement | a nominal type `a : type <: b.` whose values are values of the base type or refinement `b` | [Object types](object/types.md#refinements) |
| reflect | turn reflective data into object items of the program | [Reflection](reflection.md#reflecting-data-into-the-program) |
| reflective type | one of the prelude types `term`, `formula`, `rule`, `item`, `module` (and `sym`, `decl`, `measure`) that represent object syntax as data, without object types; `quoted A` is the typed layer over `term` | [Reflection](reflection.md) |
| reify | turn object syntax into reflective data, by a quote; a meta value of a base or shared data type at a hole is reified by `tint`, … or `T.reify` | [Reflection](reflection.md#quotes) |
| relation | an object constant `r : τ̄ -> rel`; a set of facts | [Declarations](object/declarations.md) |
| rule | an item `h̄ :- φ.` that derives the heads `h̄` for every valuation that satisfies `φ` | [Rules](object/rules.md) |
| shared data type | a type declared `T ā : data.` that exists at both stages: a meta inductive family and an object family under one name, with the derived `T.lift` and `T.reify` | [Inductive families](meta/families.md#shared-data) |
| signature | a record type used as the type of modules | [Modules](modules.md#signatures) |
| splice | `$e`: meta code that computes object code, inserted into object code | [Staging](meta/staging.md) |
| spliced code | a meta value of type `⇑τ` in object code: a term of type `τ` whose shape is not known when it is typed | [Object types](object/types.md#typing-of-rules) |
| stage | 0 for the object level, 1 for the meta level | [Staging](meta/staging.md) |
| stratum | a set of components evaluated after all relations it negates or aggregates over | [Negation](object/negation.md) |
| struct | a relation declared as a record type `s : type = { l₁ : τ₁, … }.` | [Declarations](object/declarations.md#structs) |
| subtyping edge | an item `c <: a.` that makes the fact type `c`, or the members of the open type `c`, members of the open type `a` | [Object types](object/types.md#open-types) |
| symbol | a meta value of type `sym` that refers to an object constant | [Reflection](reflection.md#symbols-and-derived-constants) |
| termination argument | descent along derivations (A) or guarded induction (B) | [Termination](object/termination.md) |
| typed atom | a `quoted A` whose type `A` is a type of facts, used as an atom | [Reflection](reflection.md#typed-atoms) |
| typed hole | an expression `?` or `?name` that stands for an expression still to be written; it is an error that reports its goal | [Functions](meta/functions.md#typed-holes) |
| typed variable | `qvar n`: the object variable named by the hint `n`, as a `quoted A` | [Reflection](reflection.md#typed-variables) |
| union | a type `τ₁ \| … \| τₙ` whose values are those of its members | [Object types](object/types.md#unions) |
| universe | `type`, the type of object types, or `Typeᵢ`, a type of meta types | [Universes](meta/universes.md) |
| valuation | an assignment of values to the variables of a rule or query | [Rules](object/rules.md#semantics) |
| value | a literal or an identity | [Facts and identity](object/facts.md#values) |
| value invention | a rule that can derive a value that did not exist before: a new constructor term or an arithmetic result | [Termination](object/termination.md#value-invention) |

## References

The reference cites the following works by the keys in the first column. A citation is the key in
parentheses after the statement it supports, with a locator after a comma: "(Lee et al. 2001,
Theorem 4)". The first citation of a work in a chapter links to this table.

| key | work |
|---|---|
| Annenkov et al. 2023 | D. Annenkov, P. Capriotti, N. Kraus, C. Sattler. *Two-Level Type Theory and Applications.* Mathematical Structures in Computer Science 33(8), 2023. [arXiv:1705.03307](https://arxiv.org/abs/1705.03307). The two-level type theory of the meta level. |
| Berent et al. 2022 | L. Berent, M. Nissl, E. Sallinger. *Complexity of Arithmetic in Warded Datalog±.* 2022. [arXiv:2202.05086](https://arxiv.org/abs/2202.05086). Type-consistency (Definition 4). |
| Cockx and Abel 2018 | J. Cockx, A. Abel. *Elaborating Dependent (Co)pattern Matching.* ICFP 2018. Case trees and index unification for clauses. |
| Gilray et al. 2024 | T. Gilray, A. Sahebolamri, Y. Sun, S. Kunapaneni, S. Kumar, K. Micinski. *Datalog with First-Class Facts.* PVLDB 18(3), 2024. [arXiv:2411.14330](https://arxiv.org/abs/2411.14330). The language DL∃!, with Skolem identity of facts, on which the object level is based. |
| Hugin definition | *Hugin: A Two-Level Typed Datalog with First-Class Facts. Formal Language Definition*, draft revision 7. The definition of the language before the redesign. Section numbers of the form "Section 6.4" in diagnostics refer to it. |
| Kaminski et al. 2017 | M. Kaminski, B. Cuenca Grau, E. V. Kostylev, B. Motik, I. Horrocks. *Foundations of Declarative Data Analysis Using Limit Datalog Programs.* IJCAI 2017. [arXiv:1705.06927](https://arxiv.org/abs/1705.06927). Limit Datalog, the source of bound columns. |
| Kovács 2022 | A. Kovács. *Staged Compilation with Two-Level Type Theory.* ICFP 2022. [doi:10.1145/3547641](https://doi.org/10.1145/3547641). Stage inference and the two-level type theory of the meta level. |
| Lee et al. 2001 | C. S. Lee, N. D. Jones, A. M. Ben-Amram. *The Size-Change Principle for Program Termination.* POPL 2001. The termination checks of both levels. |
| Stucki et al. 2018 | N. Stucki, A. Biboudis, M. Odersky. *A Practical Unification of Multi-stage Programming and Macros.* GPCE 2018. Quoted patterns with holes. |
