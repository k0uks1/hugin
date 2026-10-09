# Introduction

This is the reference of Hugin, a two-level typed Datalog. A Hugin program has two levels:

- The *object level* is Datalog∃!, a typed Datalog with stratified negation, aggregates, arithmetic and
  first-class facts. Every constructor term that a rule derives is a fact, with an identity determined
  by its content. Object programs are evaluated bottom-up to a least fixed point, and every accepted
  program terminates.
- The *meta level* is a total, dependently typed functional language, a two-level type theory, that
  computes object programs at compile time. Modules, functors, families of relations, formula
  functions, reflection of object syntax and directives are programs of the meta level.

The following program declares a type of cities and a relation of roads with three facts. It applies the
functor `tc` of the standard library to get the transitive closure of the roads, and asks which cities
can be reached from Berlin.

```hugin,run
%use "std/graph".
city : type.
berlin : city. paris : city. rome : city.
road : city -> city -> rel.
road berlin paris.
road paris rome.
road rome berlin.
roads = tc { node = city, edge = road }.
?- roads.path berlin C.
```

```output
?- roads.path berlin C.
C = berlin.
C = paris.
C = rome.
```

## Status of this reference

The reference is *normative*. It defines the language that the reference implementation accepts: when
the implementation and this reference disagree, one of them has a bug. Every Hugin example in it is
compiled, and run where its output is shown, in the continuous integration of the implementation.

The design notes in the repository (`docs/REDESIGN.md`, `docs/NOTES.md`, `docs/history/` and the other
files under `docs/`) are *historical*: they record how and why the language came to be as it is,
including alternatives that were rejected and the arguments for the soundness of its checks. They are not
a specification. Where they differ from this reference, this reference applies.

## How to read this reference

[Notation](notation.md) defines the conventions, the grammar notation and the terms used throughout, and
lists the cited works. [Lexical structure](lexical-structure.md) defines tokens, items and the precedence
of operators. [The object level](object/index.md) defines the evaluated language, from declarations and
types to termination. [The meta level](meta/index.md) defines the compile-time language and staging.
[Reflection](reflection.md), [Directives](directives.md) and [Modules](modules.md) build on the meta
level. [The prelude](prelude.md) lists the names in scope in every program, and [the standard
library](std/index.md) the modules a program imports.

The [error index](errors/index.md) lists every diagnostic code of the compiler with an explanation and
examples. It is the same text that `hugin explain <code>` prints.
