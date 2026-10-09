# Bound columns

A *bound column* is the last column of a relation, declared `min τ` or `max τ`. A relation with a bound
column keeps, for each *key* (the values of its other columns), only the best value: the least for
`min`, the greatest for `max`. Bound columns allow recursion through arithmetic where nothing decreases,
such as shortest paths, and evaluation still terminates: a value that would improve forever becomes `-∞`
or `∞`. Bound columns follow Limit Datalog ([Kaminski et al. 2017](../notation.md#references)) and its
type-consistency condition (Berent et al. 2022, Definition 4).

## Syntax

```text
BoundColumn ::= "(" NAME ":" ("min" | "max") ObjectType ")" | ("min" | "max") ObjectType
```

`dist : (v : node) -> (d : min int) -> rel.` declares the relation `dist` with key `v` and the bound
column `d`.

## Static rules

It is an error ([E0605](../errors/E0605.md)) if a bound column

- is not the last column,
- belongs to a constructor or a struct, or occurs anywhere but in a relation declaration, or
- has a type other than `int` or a refinement of `int`.

## Reading a bound column

A body atom of a relation with a bound column binds the bound column to the best value of the key. A
fact `dist v k` of a `min` column stands for all the values `k' ≥ k`, the best of which is `k`; for a
`max` column, for all `k' ≤ k`.

Rules of later components than the bound relation read its values as plain integers: the relation is
complete when they run.

## Type-consistency

Rules within the recursive component of a bound relation must read its values in a way that keeps
"keep only the best value" exact. The *limit variables* of a rule are the variables in the bound column
of its positive body atoms over bound relations of the rule's own component. A rule is *type-consistent*
if

1. the bound column of each such atom is a variable or `_`;
2. each limit variable occurs in exactly one atom, and not in another column, under `not` or in an
   aggregate;
3. every other occurrence of a limit variable is in a linear term: built from `+`, `-`, unary `-` and
   multiplication by an integer literal, with a non-zero coefficient after simplification; a variable
   `X` defined by a binding equation `X = t` over limit variables is replaced by `t`;
4. a limit variable occurs outside its atom only in the bound column of the head, if the head's relation
   has one, and in the comparisons `<`, `<=`, `>`, `>=`, not in `=` or `<>`;
5. in the head of a `min` relation, a limit variable has a positive coefficient if it comes from a `min`
   atom and a negative one if it comes from a `max` atom; dually for a `max` head;
6. in a comparison `s₁ < s₂` or `s₁ <= s₂` (with `a > b` read as `b < a`), a limit variable has in
   `s₁ - s₂` a positive coefficient if it comes from a `min` atom and a negative one if it comes from a
   `max` atom.

Conditions 5 and 6 say that improving a value read from a bound column improves the head, and keeps a
comparison true. It is an error ([E0606](../errors/E0606.md)) if a rule is not type-consistent.

The following rule is rejected: a larger distance `D` would give a smaller head value `C - D`.

```hugin,compile_fail,E0606
node : type = string.
edge : node -> node -> int -> rel.
source : node -> rel.
edge "a" "b" 1. source "a".
dist : (v : node) -> (d : min int) -> rel.
dist S 0 :- source S.
dist W (C - D) :- dist V D, edge V W C.
```

## Semantics

A relation with a bound column stores one fact per key. When a rule derives a fact whose value is better
than the stored one, the new fact replaces it; a worse or equal value is ignored.

Some values improve without end: a cycle of negative edges lowers a `min` distance in every round. Such
values become *infinite*. After rounds 4, 8, 16, … of a component, the evaluation builds the *value
propagation graph* (Kaminski et al. 2017): a node for each key, and an edge for each rule instance that
passes a value from a key in its body to the key of its head, weighted by how much the value improves.
Every key on a cycle of positive weight, and every key reachable from one, gets the value `-∞` (for
`min`) or `∞` (for `max`), which never changes again. Type-consistency guarantees that such a value
improves forever.

`∞` and `-∞` are values of bound columns only; there is no literal for them. They print as `∞` and `-∞`.
Arithmetic and comparisons extend to them: `-∞ < k < ∞` for every integer `k`, `∞ ± k = ∞`, and
`k · ∞ = ±∞` for `k ≠ 0`. The operations `∞ - ∞`, `0 · ∞` and `∞ / ∞` are undefined, and a formula that
contains one does not hold.

A bound column of a head is not value invention ([Termination](termination.md#value-invention)): only the
key columns need a termination argument.

The following program computes shortest and longest distances from a source. The cycle `e → f → e` has
negative weight, so `e`, `f` and the node `g` after them get `-∞`; the cycle `p → q → p` has positive
weight, so `longest` gives `∞` there.

```hugin,run
node : type = string.
edge : node -> node -> int -> rel.
source : node -> rel.
%input edge. %input source.
dist : (v : node) -> (d : min int) -> rel.
dist S 0 :- source S.
dist W (D + C) :- dist V D, edge V W C.
longest : (v : node) -> (d : max int) -> rel.
longest S 0 :- source S.
longest W (D + C) :- longest V D, edge V W C, C > 0.
%output dist. %output longest.
```

```facts
source "a".
edge "a" "b" 4.  edge "a" "c" 1.  edge "c" "b" 2.
edge "b" "e" 1.  edge "e" "f" (-3).  edge "f" "e" 1.  edge "f" "g" 7.
edge "a" "p" 2.  edge "p" "q" 1.  edge "q" "p" 1.
```

```output
dist "a" 0.
dist "b" 3.
dist "c" 1.
dist "e" (-∞).
dist "f" (-∞).
dist "g" (-∞).
dist "p" 2.
dist "q" 3.
longest "a" 0.
longest "b" 4.
longest "c" 1.
longest "e" 5.
longest "p" ∞.
longest "q" ∞.
```

The following program reads a `min` relation in a later component, where its values are plain integers.

```hugin,run
item : type = string.
cost : item -> int -> rel.
part : item -> item -> int -> rel.
cost "bolt" 2. cost "plate" 10.
part "frame" "plate" 2. part "frame" "bolt" 8.
cheapest : (i : item) -> (c : min int) -> rel.
cheapest I C :- cost I C.
cheapest I (C + N) :- part I P N, cheapest P C.
dearest : int -> rel.
dearest M :- M = max { C | cheapest _ C }.
%output cheapest. %output dearest.
```

```output
cheapest "bolt" 2.
cheapest "frame" 10.
cheapest "plate" 10.
dearest 10.
```

> **Note.** The value propagation graph is checked at growing intervals because building it costs a pass
> over the component's rules. A cycle of positive weight, once present, stays present, so it is found at
> the next check.
