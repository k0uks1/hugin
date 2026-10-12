# `std/eq`

The module `std/eq` defines propositions as types for proofs at the meta level: the identity family `eq`,
its eliminator and lemmas, the empty and the unit type, sums, logical equivalence, decidable
propositions, and the decidable equality of atomic values. A proof of a proposition is a meta value of
its type, and a lemma is a function from proofs to proofs. A program writes `%use "std/eq".`

| declaration | meaning |
|---|---|
| `eq : {A : Type} -> A -> A -> Type.` | `eq x y`: `x` and `y` are equal, a polymorphic family |
| `refl : {A : Type} -> {x : A} -> eq x x.` | the only proof of an equation, of `eq x x` |
| `eqElim : {A : Type} -> {x : A} -> (P : (y : A) -> eq x y -> Type) -> P x refl -> {y : A} -> (e : eq x y) -> P y e.` | the eliminator J |
| `sym : {A : Type} -> {x y : A} -> eq x y -> eq y x.` | symmetry |
| `trans : {A : Type} -> {x y z : A} -> eq x y -> eq y z -> eq x z.` | transitivity |
| `cong : {A B : Type} -> {x y : A} -> (f : A -> B) -> eq x y -> eq (f x) (f y).` | congruence |
| `subst : {A : Type} -> {x y : A} -> (P : A -> Type) -> eq x y -> P x -> P y.` | transport |
| `uip : {A : Type} -> {x y : A} -> (p q : eq x y) -> eq p q.` | K: two proofs of an equation are equal |
| `empty : Type.` | the empty type, a family without constructors |
| `emptyElim : {A : Type} -> empty -> A.` | from a proof of `empty`, anything |
| `absurdBool : {A : Type} -> eq false true -> A.` | the constructors of `bool` are distinct |
| `unit : Type.`, `tt : unit.` | the unit type and its value |
| `either : Type -> Type -> Type.` | `either A B`: a proof of `A` or one of `B` |
| `left : A -> either A B.`, `right : B -> either A B.` | the two cases |
| `iff : Type -> Type -> Type = [a] [b] { to : a -> b, from : b -> a }.` | logical equivalence |
| `dec : Type -> Type.` | `dec A`: a proof of `A` or a refutation of it |
| `yes : A -> dec A.`, `no : (A -> empty) -> dec A.` | the two cases |
| `decEq : {A : Type} -> (a b : A) -> dec (eq a b).` | the decidable equality of atomic values |
| `sameTrue : {A : Type} -> {a b : A} -> eq (same a b) true -> eq a b.` | equal atomic values are equal (primitive) |
| `apart : {A : Type} -> {a b : A} -> eq (same a b) false -> eq a b -> empty.` | distinct atomic values are not equal (primitive) |

The families are closed: no other file can add a constructor to them ([Inductive
families](../meta/families.md#syntax)). `eq` is a polymorphic family, whose implicit argument, the type
of its sides, uses infer or take [by name](../meta/functions.md#implicit-arguments-by-name):
`eq {A := int} 1 2`. `false` and `true` are those of the shared `bool` of
[`std/reflect`](reflect.md#lists-options-and-booleans), and `same` is its
[primitive](reflect.md#primitives). `sym` is symmetry here; the type of symbols of `std/reflect` has the
same name, so a program that uses both opens only the names it needs from one of them
(`%use "std/reflect" (sym).` and `%use "std/eq" (eq, refl).`), or imports one of them under a name
(`r = %import "std/reflect".`, then `r.sym`).

## Equality

`x ≡ y`, or `x == y` in ASCII, is `eq x y`: the file binds the operator `≡` to the family
([Operators bound to meta functions](../lexical-structure.md#operators-bound-to-meta-functions)),

```hugin,ignore
%infix ≡ eq.
```

so a file that opens `eq` writes `(n : nat) -> 0 + n ≡ n` for `(n : nat) -> eq (plus 0 n) n`. Types are
shown with `eq`. `=` is not the equality: it defines and compares object values.

The lemmas are ordinary functions by clauses. Matching on `refl` unifies the two sides of the equation
([Index unification](../meta/coverage.md#index-unification)), so each of them has a single clause:

```hugin,ignore
eqElim P H refl = H.
sym refl = refl.
trans refl Q = Q.
cong F refl = refl.
subst P refl H = H.
uip refl refl = refl.
emptyElim ().
absurdBool ().
```

`eqElim` is Martin-Löf's J, dependent matching on `refl` ([Cockx and Abel
2018](../notation.md#references)). `uip` holds since index unification deletes an equation `x = x` (axiom
K): any two proofs of the same equation are equal. On `refl`, the lemmas compute: `subst P refl H` is
`H`. An equation that holds by evaluation is proved by `refl` itself: `plus 2 2` evaluates to `4`, so
`refl` proves `plus 2 2 ≡ 4`.

The equation of [`match H : e`](../meta/match.md#the-equation) is `eq`, and
[`rewrite h in e`](../meta/match.md#rewrite) elaborates to `subst` and `sym`; both need a program that
loads `std/eq`.

The following program proves that `0` is a left unit of `+` on `nat`, which is `plus` of
[`std/nat`](nat.md) and recurses on its second argument, by induction with `cong`, and uses the proof to
transport a vector.

```hugin,run
%use "std/eq".
%use "std/nat".
zeroPlus : (n : nat) -> 0 + n ≡ n.
zeroPlus 0 = refl.
zeroPlus (N + 1) = cong suc (zeroPlus N).
vec : Type -> nat -> Type.
vnil : vec A 0.
vcons : A -> vec A N -> vec A (N + 1).
cast : {n : nat} -> vec int (0 + n) -> vec int n.
cast {n := N} V = subst (vec int) (zeroPlus N) V.
size : vec int N -> int.
size vnil = 0.
size (vcons _ Xs) = 1 + size Xs.
lengths : int -> rel.
lengths (size (cast {n := 3} (vcons 1 (vcons 2 (vcons 3 vnil))))).
```

```output
lengths 3.
```

`plus 0 (N + 1)` evaluates to `suc (plus 0 N)` by the second clause of `plus`, so `cong suc (zeroPlus N)`
has the type of the second clause's goal. A proof that later items need only by its statement can be made
[opaque](../meta/index.md#opaque-definitions).

## Propositions

`empty` has no constructor, so a function from it has the single absurd clause, and a value of `empty` in
a context means that the case cannot occur. `either`, `iff` and `dec` are disjunction, equivalence and
decidability; a function that matches on `left` and `right`, or `yes` and `no`, is a proof by cases.

The following function proves that a disjunction can be swapped.

```hugin
%use "std/eq".
swap : {A B : Type} -> either A B -> either B A.
swap (left X) = right X.
swap (right Y) = left Y.
```

## Decidable equality of atomic values

An *atomic value* is a literal of `float` or `string`, a meta integer, a numeral of a nat-like family, a symbol
of `sym`, or closed object code in canonical form, a value of a type `⇑A` that is an object literal, a base
type, or an object constant applied to such code (`⟨edge berlin paris⟩`): a value that
[`same`](reflect.md#primitives) compares. Object code is compared by its syntax, as index unification
compares it; object arithmetic such as `⟨1 + 2⟩` is not in canonical form. `decEq a b` is `yes refl` if `a` and `b`
are equal atomic values and `no` with a refutation if they are distinct ones; on anything else it is
stuck, as `same` is. It is defined from `same` and two primitives, which state what `same` decides as
proofs:

```hugin,ignore
decEq X Y = pick (same X Y) refl
  where
    pick : (s : bool) -> eq (same X Y) s -> dec (eq X Y).
    pick true E = yes (sameTrue E).
    pick false E = no (apart E).
```

`sameTrue {A} {a} {b} e` is `refl` if `a` and `b` are equal atomic values, and stuck otherwise. `apart`
never evaluates: its result type is empty, and no closed proof of its hypothesis `eq (same a b) false`
exists for equal atomic values. On closed distinct atomic values `a` and `b`, `apart refl` is the
function that the absurd clause `f ().` of `f : eq a b -> empty` defines: index unification refutes
`eq a b` by its conflict rule for distinct atomic values ([Index
unification](../meta/coverage.md#index-unification)). Both are trusted, as `same` is; their declarations
`= %builtin sameTrue` and `= %builtin apart` must have exactly the types in the table, with an identity
family `eq` (one constructor of type `{A : Type} -> {x : A} -> eq x x`) and a family `empty` without
constructors ([E0103](../errors/E0103.md)).

The following program decides equalities of symbols and numbers.

```hugin,run
%use "std/eq".
r = %import "std/reflect".
city : type.
berlin, paris : city.
answer : dec A -> string.
answer (yes _) = "yes".
answer (no _) = "no".
decided : string -> string -> rel.
decided "cities" (answer (decEq {A := r.sym} '( berlin ) '( paris ))).
decided "numbers" (answer (decEq {A := int} 7 7)).
```

```output
decided "cities" "no".
decided "numbers" "yes".
```

The type of the atomic values is given by name: a literal checked against an unknown type is an `int`
only at the end of its item ([Literals](../meta/functions.md#literals-and-primitive-operations)), and a
quote needs its reflective type.

> **Note.** Without universe polymorphism there is one `eq` per program, and its implicit argument `A`
> lives at the largest universe level that a program uses it at ([Universes](../meta/universes.md)). `eq`
> itself is in `Type₀`, since the implicit arguments of `refl` occur in its result type ([Universe
> levels](../meta/families.md#universe-levels)).
