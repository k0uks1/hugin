# `std/list`

The module `std/list` defines relations over the lists that are facts.

| declaration | meaning |
|---|---|
| `len : (l : list A) -> (n : int) -> rel.` | the length of every list that is a fact |

`len` is defined by guarded induction on the list:

```hugin,ignore
len nil 0.
len (cons X L) M :- cons X L, len L N, M = N + 1.
```

So `len` measures the lists that are facts. A program that asks for the length of lists it builds in rule
bodies writes `%demand len +l -n.`; the demand rules then build the lists
([Directives](../directives.md#demand)).

The following program measures a list given as a fact.

```hugin,run
%use "std/list".
words : list string -> rel.
words ["a", "b"].
?- words L, len L N.
```

```output
?- words L, len L N.
L = cons "a" (cons "b" nil), N = 2.
```
