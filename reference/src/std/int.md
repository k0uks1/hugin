# `std/int`

The meta level's integers are an inductive family, like Lean's `Int`: unbounded, with two constructors
over the natural numbers of [`std/nat`](nat.md). The family and its constructors are declared in
`std/nat`; the module `std/int` defines their arithmetic and comparisons. The
[prelude](../prelude.md) opens `ofNat`, `negSucc`, `iequal`, `iless`, `ileq` and `fits64` in every file;
a program that uses the other functions by name writes `%use "std/int".`

| declaration | meaning |
|---|---|
| `int : Type.` (in `std/nat`) | the integers of the meta level, a meta inductive family |
| `ofNat : nat -> int.` (in `std/nat`) | `ofNat n` is `n` |
| `negSucc : nat -> int.` (in `std/nat`) | `negSucc n` is `-(n + 1)` |
| `negOfNat : nat -> int.` | the negation of a natural number |
| `subNatNat : nat -> nat -> int.` | the difference of two natural numbers |
| `ineg : int -> int.` | `-x` |
| `iplus : int -> int -> int.` | `x + y` |
| `iminus : int -> int -> int.` | `x - y` |
| `itimes : int -> int -> int.` | `x * y` |
| `idiv : int -> int -> int.` | `x / y`, rounded toward zero; `x / 0` is `0` |
| `iequal : int -> int -> bool.` | whether two integers are equal |
| `iless : int -> int -> bool.` | whether the first is less than the second |
| `ileq : int -> int -> bool.` | whether the first is at most the second |
| `fits64 : int -> bool.` | whether an integer is in the object level's 64-bit range |
| `natAbs : int -> nat.` | the absolute value, as a natural number |

## The meta `int`

The name `int` denotes the base type `int` ([Object types](../object/types.md#base-types)). Where it is
a meta type, as in `limit : int = 3.` or `f : int -> int.`, it is the family `int` of `std/nat`, in every
file, also where `std/nat` is not opened; a file that opens all of `std/nat` gets the same base type
under the name `int`. Its values are `ofNat n` for the natural numbers `n` and `negSucc n` for the
negative integers `-(n + 1)`, so every integer has exactly one form, and functions on integers are defined
by clauses on the two constructors, with [coverage](../meta/coverage.md) and
[termination](../meta/termination.md) checked as for any family.

A closed integer is represented as a number, as a closed numeral of a nat-like family is
([Inductive families](../meta/families.md#numerals)), and the representation is not observable: a
pattern `ofNat N` matches `5` with `N` the numeral `5`, `negSucc N` matches `-3` with `N` the numeral `2`,
and `ofNat 5` evaluates to `5`. The family is closed: no other file can add a constructor to it.

An integer literal checked against the meta `int` is its integer, also beyond 64 bits and negative
(`-100000000000000000000`); a literal whose type is not determined otherwise is an `int` at stage 1
([Literals](../meta/functions.md#literals-and-primitive-operations)). As a pattern against `int`, an
integer literal stands for constructor patterns: `5` is `ofNat 5` and `-3`, written `(-3)`, is
`negSucc 2` ([Clauses](../meta/clauses.md#patterns)).

## Arithmetic

The operators `+`, `-`, `*` and `/` on meta integers, and the negation `-x`, apply `iplus`, `iminus`,
`itimes`, `idiv` and `ineg` of the file `std/int`, whatever the names in scope of the program; types and
diagnostics show these applications as the operators. The file also binds the four operators to these
functions, `%infix + iplus.` and so on ([Operators bound to meta
functions](../lexical-structure.md#operators-bound-to-meta-functions)): in a file that opens `std/int`,
the editor shows the function at the operator, and `+` on `int` is told apart from `+` on `nat` of
[`std/nat`](nat.md#operators) by the types. The functions are defined by clauses, as Lean
defines them (`src/Init/Data/Int/Basic.lean`), over the functions of `std/nat`:

```hugin,ignore
negOfNat 0 = 0.
negOfNat (N + 1) = negSucc N.
subNatNat M 0 = ofNat M.
subNatNat 0 (N + 1) = negSucc N.
subNatNat (M + 1) (N + 1) = subNatNat M N.
ineg (ofNat N) = negOfNat N.
ineg (negSucc N) = ofNat (N + 1).
iplus (ofNat M) (ofNat N) = ofNat (plus M N).
iplus (ofNat M) (negSucc N) = subNatNat M (N + 1).
iplus (negSucc M) (ofNat N) = subNatNat N (M + 1).
iplus (negSucc M) (negSucc N) = negSucc (plus M N + 1).
iminus X Y = iplus X (ineg Y).
itimes (ofNat M) (ofNat N) = ofNat (times M N).
itimes (ofNat M) (negSucc N) = negOfNat (times M (N + 1)).
itimes (negSucc M) (ofNat N) = negOfNat (times (M + 1) N).
itimes (negSucc M) (negSucc N) = ofNat (times (M + 1) (N + 1)).
idiv (ofNat M) (ofNat 0) = 0.
idiv (ofNat M) (ofNat (N + 1)) = ofNat (divSucAux 0 N M N).
idiv (ofNat M) (negSucc N) = negOfNat (divSucAux 0 N M N).
idiv (negSucc M) (ofNat 0) = 0.
idiv (negSucc M) (ofNat (N + 1)) = negOfNat (divSucAux 0 N (M + 1) N).
idiv (negSucc M) (negSucc N) = ofNat (divSucAux 0 N (M + 1) N).
iequal (ofNat M) (ofNat N) = equal M N.
iequal (ofNat M) (negSucc N) = false.
iequal (negSucc M) (ofNat N) = false.
iequal (negSucc M) (negSucc N) = equal M N.
iless (ofNat M) (ofNat N) = less M N.
iless (ofNat M) (negSucc N) = false.
iless (negSucc M) (ofNat N) = true.
iless (negSucc M) (negSucc N) = less N M.
ileq (ofNat M) (ofNat N) = less M (N + 1).
ileq (ofNat M) (negSucc N) = false.
ileq (negSucc M) (ofNat N) = true.
ileq (negSucc M) (negSucc N) = less N (M + 1).
fits64 (ofNat N) = less N 9223372036854775808.
fits64 (negSucc N) = less N 9223372036854775808.
natAbs (ofNat N) = N.
natAbs (negSucc N) = N + 1.
```

Division rounds toward zero, as the object level's division does (Lean's `Int.tdiv`), so `-7 / 2` is
`-3`. It is total, as division is in Lean, Rocq and Isabelle: `x / 0` is `0`. Arithmetic written in
object code is the object operation, whose division by zero is undefined
([Staging](../meta/staging.md#lifting)).

Since the functions are defined by clauses, they compute on open terms as far as their clauses do, and
proofs reason about them by cases: `x + 0` evaluates to `ofNat N` for `x` of the form `ofNat N`. The
library [`std/decide`](decide.md) has lemmas about them.

## Native arithmetic

The clauses are the definition, but the compiler computes the functions directly on numbers when all
their arguments are numerals or integers, as it does for [`std/nat`](nat.md#native-arithmetic): each takes
one step on any integers, however large.

| function | native operation | result on the integers `a`, `b` (the numerals `m`, `n`) |
|---|---|---|
| `negOfNat` | negOfNat | `-n` |
| `subNatNat` | subNatNat | `m - n` |
| `ineg` | int neg | `-a` |
| `iplus` | int add | `a + b` |
| `iminus` | int sub | `a - b` |
| `itimes` | int mul | `a × b` |
| `idiv` | int div | `a / b` rounded toward zero; `0` if `b = 0` |
| `iequal` | int eq | `true` if `a = b`, else `false` |
| `iless` | int lt | `true` if `a < b`, else `false` |
| `ileq` | int le | `true` if `a ≤ b`, else `false` |
| `fits64` | fits64 | `true` if −2⁶³ ≤ `a` ≤ 2⁶³ − 1, else `false` |
| `natAbs` | natAbs | the numeral `|a|` |

The compiler's numbers have a size limit of 2²⁴ bits, about five million decimal digits: a native sum,
difference or product whose result would be larger is not computed, and its application stays stuck,
as Lean's and Agda's numbers end where memory does. Object code that needs such a value is an error
([E0909](../errors/E0909.md)); diagnostics show an integer of more than 4096 bits by its size.

The native operations give exactly the values of the clauses: when the compiler elaborates `std/int`, it
checks each function's clauses against the defining equations of its operation, one per pair of
constructors (`iplus (ofNat m) (ofNat n) = ofNat (plus m n)`, and so on, over the checked native
operations of `std/nat`), by evaluation on variables. Since every integer is `ofNat n` or `negSucc n`, the
equations determine the function on every integer. A `std/int` whose clauses do not satisfy them is an
internal error of the compiler. The operations are bound to the functions of the library file itself;
a program's own function with the same clauses computes by its clauses. The native functions are trusted
primitives of the meta level ([Consistency](../meta/consistency.md#assumptions)).

## Integers in object code

The object level's `int` stays 64-bit. A meta integer used as object code is persisted as a literal
([Staging](../meta/staging.md#lifting)), and it must lie between −9223372036854775808 and
9223372036854775807: it is an error ([E0930](../errors/E0930.md)) otherwise, where the value crosses into
object code, never a wrapped number. `fits64` tests the range, for proofs and for code that branches on
it.

## Examples

The following program computes with integers beyond 64 bits at compile time and uses the results that
fit as object code.

```hugin,run
%use "std/int" (idiv, natAbs).
%use "std/nat" (toInt).
googol : int = 10000000000 * 10000000000 * 10000000000 * 10000000000 * 10000000000 * 10000000000 * 10000000000 * 10000000000 * 10000000000 * 10000000000.
fact : nat -> int.
fact 0 = 1.
fact (N + 1) = ofNat (N + 1) * fact N.
sign : int -> int.
sign 0 = 0.
sign (ofNat (N + 1)) = 1.
sign (negSucc N) = -1.
result : string -> int -> rel.
result "digits" (googol / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000).
result "30! / 28!" (fact 30 / fact 28).
result "30! fits" (if (fits64 (fact 30)) 1 0).
result "sign" (sign (-5 - googol)).
result "truncated" (idiv (-7) 2).
result "distance" (toInt (natAbs (3 - 10))).
```

```output
result "30! / 28!" 870.
result "30! fits" 0.
result "digits" 10000000.
result "distance" 7.
result "sign" (-1).
result "truncated" (-3).
```

The following program compares meta integers, which the meta level has no operators for, with the
functions of the prelude.

```hugin,run
clamp : int -> int -> int -> int.
clamp Lo Hi X = if (iless X Lo) Lo (if (iless Hi X) Hi X).
shown : int -> rel.
shown (clamp 0 10 (-4)).
shown (clamp 0 10 25).
shown (if (iequal (2 * 3) 6) 1 0).
```

```output
shown 0.
shown 1.
shown 10.
```
