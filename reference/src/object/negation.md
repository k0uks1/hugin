# Negation and stratification

A negated atom `not r t̄` holds if the database has no fact that matches `r t̄`. Negation is evaluated
under the closed-world reading: what is not derived is false. For this reading to be well defined, a
relation must be complete before it is negated. This chapter defines negation, the stratification that
orders evaluation, and the completeness discipline for relations that are open to more facts.

## Negation

```text
Negation ::= "not" Atom
```

`not r t₁ … tₙ` holds under a valuation if no fact `r v₁ … vₙ` matches `t₁ … tₙ`. The variables of the
atom that the rest of the body binds must be bound before the negation is evaluated
([range restriction](rules.md#range-restriction)). A variable that occurs only in the negated atom, such
as a wildcard, is local to it: the negation holds if no value of it gives a fact.

The following program finds the people without children. The wildcard in `not parent X _` is local to
the negation.

```hugin,run
person : type.
alice : person. bob : person. carol : person.
parent : person -> person -> rel.
parent alice bob.
parent alice carol.
known : person -> rel.
known alice. known bob. known carol.
childless : person -> rel.
childless X :- known X, not parent X _.
%output childless.
```

```output
childless bob.
childless carol.
```

## Stratification

Negations and [aggregates](aggregates.md) are *negative* edges of the dependency graph
([Evaluation](index.md#evaluation)). A program is *stratified* if no component contains a negative edge,
that is, no relation depends on itself through a negation or an aggregate. Then every negated or
aggregated relation belongs to an earlier component than the rule that reads it, and is complete when the
rule is evaluated. The components between two negative edges form a *stratum*.

It is an error ([E0601](../errors/E0601.md)) if a program is not stratified. The diagnostic shows the
cycle.

The following program is not stratified: `p` and `q` negate each other.

```hugin,compile_fail,E0601
base : int -> rel.
base 1.
p : int -> rel.
q : int -> rel.
p X :- base X, not q X.
q X :- base X, not p X.
```

A rule whose head builds a fact of a constructor `c` makes `c` depend on the rule's body
([Facts and identity](facts.md#facts-derived-in-other-components)). Such a rule cannot negate a relation
that depends on `c`.

## Completeness

A relation is *open* if it is declared with the directive `%open`: its facts may come from a facts file,
and the program does not claim to know all of them. A relation is *incomplete* if it is open or depends
positively on an incomplete relation. The absence of a fact of an incomplete relation means "unknown",
not "false", so

- it is an error ([E0602](../errors/E0602.md)) if a rule negates or aggregates over an incomplete
  relation, and
- a query may mention an incomplete relation only positively (also [E0602](../errors/E0602.md)).

A relation declared `%input` is complete: its facts file states all of its facts. The
[input relations](io.md#input-facts) are those declared `%input` or `%open`.

The following program negates an open relation and is rejected.

```hugin,compile_fail,E0602
user : type.
login : user -> rel.
%open login.
known : user -> rel.
%input known.
inactive : user -> rel.
inactive U :- known U, not login U.
```

A functor that negates or aggregates over a relation of its parameter declares the requirement
`%complete` in its signature ([Modules](../modules.md#signatures)).
