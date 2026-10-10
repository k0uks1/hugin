# `std/order`

The module `std/order` defines the best items by a score, rankings and top-k, and the order of a finite
set of numbers. Its functors aggregate over the relations of their arguments, so the signatures require
them to be [complete](../object/negation.md#completeness). A program opens the module with
`%use "std/order".`

| declaration | meaning |
|---|---|
| `scores : Type = { key : type, item : type, score : key -> item -> int -> rel, %complete score }.` | a score for items, grouped by a key |
| `best (s : scores)` | `argmin K X` and `argmax K X`: the items with the least and the greatest score of their key |
| `ranking (s : scores)` | `rank K X R`: one more than the number of items of `K` with a greater score |
| `top (s : scores) (n : int)` | `top K X`: the items of rank at most `n` |
| `ints : Type = { elem : int -> rel, %complete elem }.` | a finite set of numbers |
| `order (d : ints)` | `first X`, `next X Y` (the next greater element) and `position X N` (the number of smaller elements) |

Ties are kept: the items with the same score have the same rank, and `top s 1` holds for all the items
with the greatest score, as SQL's `RANK`. Grouping needs no combinator: an aggregate groups by the
variables it shares with its rule ([Aggregates](../object/aggregates.md)), here the key.

## Scores

`best` gives the items with the least and the greatest score of each key.

```hugin,run
%use "std/order".
team : type. red : team. blue : team.
person : type. ann : person. bob : person. cid : person. dan : person.
points : team -> person -> int -> rel.
points red ann 7. points red bob 9. points red cid 9. points blue dan 3.
b = best { key = team, item = person, score = points }.
%output b.argmin. %output b.argmax.
```

```output
b.argmax blue dan.
b.argmax red bob.
b.argmax red cid.
b.argmin blue dan.
b.argmin red ann.
```

`ranking` ranks the items of each key; equal scores share a rank.

```hugin,run
%use "std/order".
team : type. red : team.
person : type. ann : person. bob : person. cid : person.
points : team -> person -> int -> rel.
points red ann 7. points red bob 9. points red cid 9.
r = ranking { key = team, item = person, score = points }.
%output r.rank.
```

```output
r.rank red ann 3.
r.rank red bob 1.
r.rank red cid 1.
```

`top` keeps the items of rank at most `n`.

```hugin,run
%use "std/order".
team : type. red : team. blue : team.
person : type. ann : person. bob : person. cid : person. dan : person.
points : team -> person -> int -> rel.
points red ann 7. points red bob 9. points red cid 8. points blue dan 3.
t = top { key = team, item = person, score = points } 2.
%output t.top.
```

```output
t.top blue dan.
t.top red bob.
t.top red cid.
```

## Order of numbers

`order` gives the first element of a finite set of numbers, the successor of each element and its
position, counted from 0.

```hugin,run
%use "std/order".
day : int -> rel.
day 3. day 10. day 7.
od = order { elem = day }.
%output od.first. %output od.next. %output od.position.
```

```output
od.first 3.
od.next 3 7.
od.next 7 10.
od.position 10 2.
od.position 3 0.
od.position 7 1.
```
