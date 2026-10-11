# `std/nat`

The module `std/nat` defines the natural numbers of the meta level and the arithmetic on them, and the
family of the meta integers built on them, whose arithmetic is [`std/int`](int.md). The
[prelude](../prelude.md) opens `nat`, `zero`, `suc`, `ofNat` and `negSucc` in every file; a program that
uses the functions writes `%use "std/nat".`

| declaration | meaning |
|---|---|
| `nat : Type.` | the natural numbers, a meta inductive family |
| `zero : nat.` | zero |
| `suc : nat -> nat.` | the successor |
| `plus : nat -> nat -> nat.` | the sum, by recursion on the second argument |
| `minus : nat -> nat -> nat.` | the truncated difference: `0` if the second argument is the larger |
| `times : nat -> nat -> nat.` | the product, by recursion on the second argument |
| `divSucAux : nat -> nat -> nat -> nat -> nat.` | division by a successor: `divSucAux 0 d n d` is `n` divided by `d + 1`, rounded down |
| `modSucAux : nat -> nat -> nat -> nat -> nat.` | the remainder: `modSucAux 0 d n d` is the remainder of `n` divided by `d + 1` |
| `equal : nat -> nat -> bool.` | whether two natural numbers are equal |
| `less : nat -> nat -> bool.` | whether the first is less than the second |
| `int : Type.` | the integers of the meta level, a meta inductive family ([`std/int`](int.md)) |
| `ofNat : nat -> int.` | the integer `n` |
| `negSucc : nat -> int.` | the integer `-(n + 1)` |
| `toInt : nat -> int.` | the meta integer of a natural number, `ofNat` |

`nat` is nat-like, so integer literals and successor patterns `N + k` denote its values
([Inductive families](../meta/families.md#numerals)). `equal` and `less` return the shared `bool` of
[`std/reflect`](reflect.md#lists-options-and-booleans). The functions are defined by clauses:

```hugin,ignore
plus N 0 = N.
plus N (M + 1) = plus N M + 1.
minus N 0 = N.
minus 0 (M + 1) = 0.
minus (N + 1) (M + 1) = minus N M.
times N 0 = 0.
times N (M + 1) = plus (times N M) N.
divSucAux K M 0 J = K.
divSucAux K M (N + 1) 0 = divSucAux (K + 1) M N M.
divSucAux K M (N + 1) (J + 1) = divSucAux K M N J.
modSucAux K M 0 J = K.
modSucAux K M (N + 1) 0 = modSucAux 0 M N M.
modSucAux K M (N + 1) (J + 1) = modSucAux (K + 1) M N J.
equal 0 0 = true.
equal 0 (M + 1) = false.
equal (N + 1) 0 = false.
equal (N + 1) (M + 1) = equal N M.
less N 0 = false.
less 0 (M + 1) = true.
less (N + 1) (M + 1) = less N M.
toInt N = ofNat N.
```

`divSucAux` and `modSucAux` are Agda's `div-helper` and `mod-helper`: `divSucAux k m n j` counts in `k`
how often `n` steps exhaust the counter `j`, which restarts at `m`. A division by `d` is a function that
handles `d = 0` itself:

```hugin,ignore
div : nat -> nat -> nat.
div N 0 = 0.
div N (D + 1) = divSucAux 0 D N D.
```

Since `plus` splits on its second argument, `plus N k` for a numeral `k` evaluates to `N + k` also when
`N` is not known.

## Native arithmetic

The clauses are the definition of the functions, but the compiler computes them directly on numbers
when all their arguments are numerals, as Agda's built-in natural numbers and Lean 4's `Nat` do: `plus`,
`minus`, `times`, `divSucAux`, `modSucAux`, `equal` and `less` take one step on any numerals,
however large, instead of one step per successor. `times 123456789 987654321` is the numeral
`121932631112635269` at once.

| function | native operation | result on the numerals `a`, `b` (`k`, `m`, `n`, `j`) |
|---|---|---|
| `plus` | add | `a + b` |
| `minus` | monus | `a - b` if `a ≥ b`, else `0` |
| `times` | mul | `a × b` |
| `divSucAux` | divSucAux | `k + ⌊max(0, n + m - j) / (m + 1)⌋` |
| `modSucAux` | modSucAux | `(n - j - 1) mod (m + 1)` if `n > j`, else `k + n` |
| `equal` | eq | `true` if `a = b`, else `false` |
| `less` | lt | `true` if `a < b`, else `false` |

The native operations give exactly the values of the clauses: when the compiler elaborates `std/nat`,
it checks each function's clauses against the defining equations of its operation (`plus n 0 = n` and
`plus n (suc m) = suc (plus n m)`, and so on), by evaluation on variables, as Agda does for its built-in
operations. The equations determine the function on every numeral, so the representation is not
observable; a `std/nat` whose clauses do not satisfy them is an internal error of the compiler.

The operations are bound to the functions of the library file `std/nat` itself, not to their names: a
function that a program defines, such as its own `plus` with the same clauses or arithmetic on a
nat-like family of its own, computes by its clauses (its numerals are still numbers,
[Inductive families](../meta/families.md#numerals)).

On arguments that are not all numerals, such as a variable of a clause, the clauses run as for any
function ([Clauses](../meta/clauses.md#evaluation)), with one shortcut: `plus N k` of a numeral `k` is
the offset `N + k` in one step, which its clauses give after `k` steps, so `plus N 100001` takes no
longer than `plus N 1`. `plus N 3` evaluates to `N + 3`, `less (N + 3) 3` to
`false`, and `times N 2` stays `plus (plus 0 N) N` while `N` is not known. Types that use the functions
compute with them as before: a `vec A (plus N 1)` is a `vec A (N + 1)`.

`toInt` of a numeral is the integer in one step, also beyond 64 bits: `ofNat` applied to a numeral is an
integer, which is represented as a number as well ([`std/int`](int.md#the-meta-int)). Meta integers are
unbounded; one that does not fit into 64 bits is an error where object code uses it
([E0927](../errors/E0927.md)), never a wrapped number.

`nat` is a meta type: it has no lifting to object code, so a natural number in an object position is an
error ([E0902](../errors/E0902.md)). `toInt` converts it to an `int`, which is persisted as an object
integer if it fits ([Staging](../meta/staging.md#lifting)).

[`std/list`](list.md#fuel) uses `nat` as fuel: `size` and `iterate`.

A program that declares a name of `std/nat` itself shadows the prelude's: with its own
`nat : Type. zero : nat. suc : nat -> nat.`, its literals are numerals of its own `nat`.

## Examples

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

The following program computes with large numerals: each operation takes one step.

```hugin,run
%use "std/nat".
div : nat -> nat -> nat.
div N 0 = 0.
div N (D + 1) = divSucAux 0 D N D.
mod : nat -> nat -> nat.
mod N 0 = N.
mod N (D + 1) = modSucAux 0 D N D.
big : nat = times 123456789 987654321.
result : (name : string) -> (n : int) -> rel.
result "product" (toInt big).
result "quotient" (toInt (div big 1000000007)).
result "remainder" (toInt (mod big 1000000007)).
result "difference" (toInt (minus 10 big)).
result "less" (if (less big (plus big 1)) 1 0).
```

```output
result "difference" 0.
result "less" 1.
result "product" 121932631112635269.
result "quotient" 121932630.
result "remainder" 259106859.
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
