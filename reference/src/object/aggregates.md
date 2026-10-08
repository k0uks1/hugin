# Aggregates

An *aggregate* computes a number or a value from all solutions of a formula: their count, the sum of a
term over them, or its minimum or maximum. Aggregates are stratified like negation.

## Syntax

```text
Aggregate ::= VAR "=" AggOp "{" Term "|" Formula "}"
AggOp     ::= "count" | "sum" | "min" | "max"
```

An aggregate is a formula. Its *result variable* is the variable before `=`, its *term* is the term
before `|`, and its *body* is the formula after `|`. It is an error ([E0202](../errors/E0202.md)) if an
aggregate is not the right side of an equation with a variable on the left.

## Grouping and local variables

The variables of an aggregate's body that are bound before the aggregate, in the canonical order of the
rule ([range restriction](rules.md#range-restriction)), are its *grouping variables*. The other variables
of the body and the term are *local* to the aggregate. For each valuation of the grouping variables, the
aggregate ranges over the distinct valuations of its local variables that satisfy its body.
Wildcards are local variables as well: `count { I | sale S I _ }` counts the sales of `S`, not the
distinct items, since two sales of one item at different prices are two valuations.

The term's variables must be bound by the body.

## Semantics

Let *S* be the set of distinct valuations of the local variables that satisfy the body, and *t*(σ) the
value of the term under σ ∈ *S*.

| aggregate | value | when *S* is empty |
|---|---|---|
| `X = count { t \| φ }` | the number of elements of *S* | 0 |
| `X = sum { t \| φ }` | the sum of *t*(σ) over *S* | 0 |
| `X = min { t \| φ }` | the least *t*(σ) | the formula does not hold |
| `X = max { t \| φ }` | the greatest *t*(σ) | the formula does not hold |

The sum counts *t*(σ) once per valuation σ, so equal values of different valuations are added each time.
If `X` is bound before the aggregate, the aggregate is a test: it holds if the value equals `X`.

The result of `count` is an `int`. The term of `sum` is an `int` or a `float`, and the result has its
type. The term of `min` and `max` is of a base type, ordered as by the comparisons
([Arithmetic and comparisons](arithmetic.md#comparisons)). It is an error ([E0402](../errors/E0402.md))
otherwise. An undefined sum makes the formula not hold.

The following program counts the items and sums the prices per shop, and finds the cheapest price
overall. The shop `S` is a grouping variable; `I` and `P` are local.

```hugin,run
sale : (shop : string) -> (item : string) -> (price : int) -> rel.
sale "north" "pen" 3.
sale "north" "ink" 7.
sale "south" "pen" 4.
sale "south" "pad" 4.
shop : string -> rel.
shop S :- sale S _ _.
summary : string -> int -> int -> rel.
summary S N R :- shop S, N = count { I | sale S I _ }, R = sum { P | sale S _ P }.
cheapest : int -> rel.
cheapest M :- M = min { P | sale _ _ P }.
%output summary. %output cheapest.
```

```output
cheapest 3.
summary "north" 2 10.
summary "south" 2 8.
```

In `summary "south"`, the two sales at price 4 are different valuations of the local variables `I` and
`P`, so both are added.

## Stratification

An aggregate reads the relations of its body as a negation does: they are negative edges of the
dependency graph, and it is an error ([E0601](../errors/E0601.md)) if a relation depends on itself
through an aggregate ([Negation and stratification](negation.md#stratification)). An aggregate over an
[incomplete](negation.md#completeness) relation is an error ([E0602](../errors/E0602.md)). Within the
recursion of a [bound column](bound-columns.md), the best value per key is kept without an aggregate.

## Disjunctions in aggregates

The body of an aggregate may contain a disjunction. The compiler moves the disjunction into an
auxiliary relation with one rule per alternative. Its columns are the variables of the disjunction that
are bound before it and those that every alternative binds; a variable that only some alternatives bind
is local to its alternative.

The following program counts the values in `p` or in the first column of `q`.

```hugin,run
p : int -> rel. p 1. p 2. p 3.
q : int -> int -> rel. q 1 10. q 5 50.
n : int -> rel.
n C :- C = count { X | p X ; q X _ }.
%output n.
```

```output
n 4.
```
