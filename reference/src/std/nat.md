# `std/nat`

The module `std/nat` defines the natural numbers of the meta level and two functions over them. The
[prelude](../prelude.md) opens `nat`, `zero` and `suc` in every file; a program that uses the functions
writes `%use "std/nat".`

| declaration | meaning |
|---|---|
| `nat : Type.` | the natural numbers, a meta inductive family |
| `zero : nat.` | zero |
| `suc : nat -> nat.` | the successor |
| `plus : nat -> nat -> nat.` | the sum, by recursion on the second argument |
| `toInt : nat -> int.` | the meta integer of a natural number |

`nat` is nat-like, so integer literals and successor patterns `N + k` denote its values
([Inductive families](../meta/families.md#numerals)). The functions are defined by clauses:

```hugin,ignore
plus N 0 = N.
plus N (M + 1) = plus N M + 1.
toInt 0 = 0.
toInt (N + 1) = toInt N + 1.
```

Since `plus` splits on its second argument, `plus N k` for a numeral `k` evaluates to `N + k` also when
`N` is not known.

`nat` is a meta type: it has no lifting to object code, so a natural number in an object position is an
error ([E0902](../errors/E0902.md)). `toInt` converts it to an `int`, which is persisted as an object
integer ([Staging](../meta/staging.md#lifting)).

[`std/list`](list.md#fuel) uses `nat` as fuel: `size` and `iterate`.

A program that declares a name of `std/nat` itself shadows the prelude's: with its own
`nat : Type. zero : nat. suc : nat -> nat.`, its literals are numerals of its own `nat`.

The following program computes with `plus` at compile time and converts the result with `toInt`.

```hugin,run
%use "std/nat".
triple : nat -> nat.
triple N = plus N (plus N N).
size : int -> rel.
size (toInt (triple 4 + 1)).
```

```output
size 13.
```

The following program declares its own `nat`, with other names for the constructors. Its literals and
successor patterns denote values of that `nat`.

```hugin,run
nat : Type.
none : nat.
next : nat -> nat.
measure : nat -> int.
measure 0 = 0.
measure (N + 1) = measure N + 1.
shown : int -> rel.
shown (measure (next (next none))).
```

```output
shown 2.
```
