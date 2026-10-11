# `std/list`

The module `std/list` defines functions over meta lists, fuel for fixed points at compile time, and
relations over the lists that are facts. A program opens it with `%use "std/list".` The lists are the shared lists of [`std/reflect`](reflect.md): a meta list computed
by these functions is used as an object list where one is expected
([Staging](../meta/staging.md#lifting)).

| declaration | meaning |
|---|---|
| `map : (A -> B) -> list A -> list B` | applies a function to every element |
| `filter : (A -> bool) -> list A -> list A` | the elements that satisfy a predicate, in order |
| `foldr : (A -> B -> B) -> B -> list A -> B` | `foldr f z [x₁, …, xₙ]` is `f x₁ (… (f xₙ z))` |
| `foldl : (B -> A -> B) -> B -> list A -> B` | `foldl f z [x₁, …, xₙ]` is `f (… (f z x₁)) xₙ` |
| `length : list A -> int` | the number of elements |
| `concat : list (list A) -> list A` | the concatenation of a list of lists |
| `reverse : list A -> list A` | the elements in reverse order |
| `zip : list A -> list B -> list { fst : A, snd : B }` | the pairs of elements at the same positions, as long as the shorter list |
| `any : (A -> bool) -> list A -> bool` | whether some element satisfies a predicate |
| `all : (A -> bool) -> list A -> bool` | whether every element satisfies a predicate |
| `elem : A -> list A -> bool` | whether an atom is an element |
| `diff : list A -> list A -> list A` | the elements of the first list that are not elements of the second, in order |
| `lookup : K -> list { key : K, value : V } -> option V` | the value of the first entry with a key |
| `size : list A -> nat` | the number of elements, as a `nat` |
| `iterate : nat -> (A -> A) -> A -> A` | `iterate n f x` applies `f` to `x` `n` times |
| `len : (l : list A) -> (n : int) -> rel` | the length of every list that is a fact |
| `member : (l : list A) -> (x : A) -> rel` | the elements of every list that is a fact |

## Meta functions

The meta functions are total: they are defined by clauses and are structurally recursive. Pairs and
entries are records (`{ fst = x, snd = y }`, `{ key = k, value = v }`). `elem`, `diff` and `lookup`
compare elements and keys with `same`, so they apply to lists of atoms: numbers, strings and symbols.
Equality of constructed values is a function by clauses of its type, which a program writes itself.
`filter`, `any`, `all`, `elem` and `lookup` choose with `if`, which evaluates both of its arguments; meta
applications are memoised, so this costs no more than one traversal.

`map` applies a function to every element.

```hugin,run
%use "std/list".
tens : list int -> rel.
tens (map ([x] x * 10) [1, 2, 3]).
%output tens.
```

```output
tens (cons 10 (cons 20 (cons 30 nil))).
```

`filter` keeps the elements that satisfy a predicate.

```hugin,run
%use "std/list".
small : list int -> rel.
small (filter ([x] elem x [1, 2]) [3, 1, 2, 3]).
%output small.
```

```output
small (cons 1 (cons 2 nil)).
```

`foldr` combines the elements from the right.

```hugin,run
%use "std/list".
total : int -> rel.
total (foldr ([x] [s] x + s) 0 [1, 2, 3]).
shown : string -> rel.
shown (foldr ([x] [s] "(" ^ x ^ s ^ ")") "" ["a", "b"]).
%output total. %output shown.
```

```output
shown "(a(b))".
total 6.
```

`foldl` combines the elements from the left.

```hugin,run
%use "std/list".
shown : string -> rel.
shown (foldl ([s] [x] "(" ^ s ^ x ^ ")") "" ["a", "b"]).
%output shown.
```

```output
shown "((a)b)".
```

`length` counts the elements of a meta list; `len` (below) measures the lists that are facts.

```hugin,run
%use "std/list".
number : int -> rel.
number (length ["a", "b", "c"]).
%output number.
```

```output
number 3.
```

`concat` concatenates a list of lists.

```hugin,run
%use "std/list".
flat : list int -> rel.
flat (concat [[1, 2], [], [3]]).
%output flat.
```

```output
flat (cons 1 (cons 2 (cons 3 nil))).
```

`reverse` reverses a list.

```hugin,run
%use "std/list".
back : list int -> rel.
back (reverse [1, 2, 3]).
%output back.
```

```output
back (cons 3 (cons 2 (cons 1 nil))).
```

`zip` pairs the elements at the same positions; the pairs are records with the fields `fst` and
`snd`.

```hugin,run
%use "std/list".
product : { fst : int, snd : int } -> int.
product P = P.fst * P.snd.
products : list int -> rel.
products (map product (zip [1, 2, 3] [10, 20])).
%output products.
```

```output
products (cons 10 (cons 40 nil)).
```

`any` and `all` test a predicate on the elements.

```hugin,run
%use "std/list".
some_three : bool -> rel.
some_three (any ([x] same x 3) [3, 1, 2]).
all_three : bool -> rel.
all_three (all ([x] same x 3) [3, 1, 2]).
%output some_three. %output all_three.
```

```output
all_three false.
some_three true.
```

`elem` tests whether an atom is an element.

```hugin,run
%use "std/list".
known : bool -> rel.
known (elem "b" ["a", "b"]).
known (elem "c" ["a", "b"]).
%output known.
```

```output
known false.
known true.
```

`diff` removes the elements of a second list.

```hugin,run
%use "std/list".
rest : list int -> rel.
rest (diff [3, 1, 2, 3] [3]).
%output rest.
```

```output
rest (cons 1 (cons 2 nil)).
```

`lookup` finds the value of the first entry with a key, as an `option`.

```hugin,run
%use "std/list".
name : option string -> rel.
name (lookup 2 [{ key = 1, value = "one" }, { key = 2, value = "two" }]).
name (lookup 3 [{ key = 1, value = "one" }]).
%output name.
```

```output
name (some "two").
name none.
```

## Fuel

A meta function must be structurally recursive ([Termination of meta functions](../meta/termination.md)),
so a fixed point at compile time iterates a step a bounded number of times. The `nat` of
[`std/nat`](nat.md), which the prelude opens, is the type of such bounds: `size` gives the number of elements of a list as a `nat`, and `iterate n f x` applies `f` to `x`
`n` times.

`size` measures a list as a `nat`.

```hugin,run
%use "std/list".
twice : nat -> nat.
twice zero = zero.
twice (suc N) = suc (suc (twice N)).
number : int -> rel.
number (length (iterate (twice (size ["a", "b"])) ([l] 0 :: l) [])).
%output number.
```

```output
number 4.
```

`iterate` closes a set of nodes under the edges of a graph known at compile time: as many steps as there
are edges suffice.

```hugin,run
%use "std/list".
edge : Type = { src : int, dst : int }.
graph : list edge = [{ src = 1, dst = 2 }, { src = 2, dst = 3 }, { src = 4, dst = 5 }].
step : list int -> list int.
step R = foldl ([acc] [x] if (elem x acc) acc (x :: acc)) R (concat (map (targets R) graph)).
targets : list int -> edge -> list int.
targets R E = if (elem E.src R) ([E.dst]) [].
reached : list int -> rel.
reached (reverse (iterate (size graph) step [1])).
%output reached.
```

```output
reached (cons 1 (cons 2 (cons 3 nil))).
```

## Relations over lists that are facts

`len` and `member` are defined by guarded induction on the list: the guard `cons X L` in each rule makes
the tail `L` a smaller fact ([Termination](../object/termination.md)).

```hugin,ignore
len nil 0.
len (cons X L) M :- cons X L, len L N, M = N + 1.
member (cons X L) X :- cons X L.
member (cons X L) Y :- cons X L, member L Y.
```

So they hold for the lists that are facts. A program that asks for the length of lists it builds in rule
bodies writes `%demand len +l -n.`; the demand rules then build the lists
([Directives](../directives.md#demand)). A list known at compile time is measured by `length`.

`len` measures a list given as a fact.

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

`member` gives the elements of a list given as a fact.

```hugin,run
%use "std/list".
basket : list int -> rel.
basket [3, 4, 5].
?- basket L, member L X.
```

```output
?- basket L, member L X.
L = cons 3 (cons 4 (cons 5 nil)), X = 3.
L = cons 3 (cons 4 (cons 5 nil)), X = 4.
L = cons 3 (cons 4 (cons 5 nil)), X = 5.
```
