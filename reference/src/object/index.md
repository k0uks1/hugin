# The object level: Datalog∃!

The *object level* is the part of Hugin that is evaluated: a typed Datalog with stratified negation,
aggregates, arithmetic and first-class facts. Its logic is Datalog∃! (Gilray et al. 2024): every
constructor term that a rule derives is a fact, and its identity is determined by its content. This
chapter gives an overview of object programs and of their evaluation; the chapters below define each
construct.

## Object programs

An *object program* consists of

- declarations of *object constants*: object types, relations and constructors
  ([Declarations](declarations.md), [Object types](types.md));
- *rules*, which derive facts from facts ([Rules](rules.md)), and ground rules without a body, which
  state facts;
- *queries*, which ask for the valuations that satisfy a formula ([Queries and output](io.md));
- directives that mark relations as input or output, name termination measures or ask for derivation
  facts ([Directives](../directives.md)).

A Hugin file also contains meta-level items: definitions, functions and modules. The meta level runs at
compile time and produces object code ([The meta level](../meta/index.md)). The object program is what
remains after this *staging*. Every example of this chapter is an object program without meta code,
except that it uses the [prelude](../prelude.md).

The following program declares a relation of edges with three facts and a relation of paths with two
rules, and asks which nodes are reachable from `1`.

```hugin,run
edge : int -> int -> rel.
edge 1 2.
edge 2 3.
edge 3 1.
path : int -> int -> rel.
path X Y :- edge X Y.
path X Z :- edge X Y, path Y Z.
?- path 1 Z.
```

```output
?- path 1 Z.
Z = 1.
Z = 2.
Z = 3.
```

## Static checks

An object program is valid if it passes the following checks, in this order. Each is defined in the
chapter given.

1. Typing: every term has a type that fits its position ([Object types](types.md#typing-of-rules)).
2. Range restriction: every variable is bound by the body of its rule ([Rules](rules.md#range-restriction)).
3. Stratification: no relation depends on itself through negation or an aggregate
   ([Negation](negation.md#stratification)).
4. Bound columns are well placed and read in a type-consistent way ([Bound columns](bound-columns.md)).
5. Completeness: no rule negates or aggregates over an incomplete relation
   ([Negation](negation.md#completeness)).
6. Termination: every recursive component has a finite fixed point ([Termination](termination.md)).

A program that passes these checks has a unique meaning, and its evaluation terminates for every input.

## Evaluation

The meaning of a program is a *database*: a set of facts. It is computed as follows.

The *dependency graph* has a node for every relation and constructor, and an edge from `r` to `s` if
a rule of `r` reads `s`. A rule reads the relations of its body atoms and the constructors whose
existence its binding equations check ([Facts and identity](facts.md#bodies-never-create-facts)). An edge
is *negative* if the reading occurrence is under `not` or inside an aggregate. A rule whose head builds a
constructor term `c t̄` also makes `c` depend on everything the rule reads.

A *component* is a strongly connected component of the dependency graph. A component is *recursive* if
it has an edge within itself. The components are evaluated one at a time, in an order in which every
component comes after the components it depends on. Evaluating a component computes the least set of
facts that is closed under its rules, given the facts of the earlier components. This is the least fixed
point of the rules; the implementation computes it by semi-naive iteration, in *rounds*.

The input facts are loaded before evaluation. The queries are answered after the last component.

> **Note.** The order of the components is not unique. Stratification guarantees that every order
> compatible with the dependency graph gives the same database, and termination guarantees that every
> component reaches its fixed point after finitely many rounds.

## Chapters

- [Declarations](declarations.md): relations, constructors, columns and labels.
- [Object types](types.md): base types, open types, refinements, unions, families and the typing of rules.
- [Facts and identity](facts.md): first-class facts, identities, and the reading of constructor terms.
- [Rules](rules.md): heads, formulas, variables, range restriction and records.
- [Arithmetic and comparisons](arithmetic.md).
- [Negation and stratification](negation.md), with the completeness discipline.
- [Aggregates](aggregates.md).
- [Bound columns](bound-columns.md): relations that keep the best value per key.
- [Termination](termination.md): why every accepted program terminates.
- [Queries, input and output](io.md).
