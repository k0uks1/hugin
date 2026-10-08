# The object level: Datalog∃!

> **Scope.** The relational language that is evaluated: types, relations, items and the overall evaluation model (least fixed point).

*To be written in redesign Phase D.*

For orientation, a complete object-level program: a relation given by facts, two rules and a query.

```hugin,run
edge : int -> int -> rel.
edge 1 2.
edge 2 3.
path : int -> int -> rel.
path X Y :- edge X Y.
path X Z :- edge X Y, path Y Z.
?- path 1 Z.
```

```output
?- path 1 Z.
Z = 2.
Z = 3.
```
