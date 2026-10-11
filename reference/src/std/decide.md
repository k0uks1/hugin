# `std/decide`

The module `std/decide` supports *proof by evaluation*: a proposition about a closed value is proved by
running a boolean check on it, as with Rocq's ssreflect `reflect` and Lean's `decide`. It also has the
soundness lemmas of the comparisons of [`std/nat`](nat.md) and [`std/int`](int.md), and basic lemmas
about their arithmetic. It builds on [`std/eq`](eq.md). A program writes `%use "std/decide".`

| declaration | meaning |
|---|---|
| `so : bool -> Type.` | `so b`: the boolean `b` is `true`, as a proposition |
| `decider : (A : Type) -> (A -> Type) -> Type = [a] [p] { check : a -> bool, sound : (x : a) -> so (check x) -> p x }.` | a decider of the property `p` of values of `a` |
| `decide : {A : Type} -> {P : A -> Type} -> (d : decider A P) -> (x : A) -> so (d.check x) -> P x.` | `decide d x tt` proves `P x` if `d.check x` evaluates to `true` |
| `soEq : (b : bool) -> so b -> eq b true.` | `so b` as an equation |
| `eqSo : (b : bool) -> eq b true -> so b.` | an equation as `so b` |
| `equalSound : (m n : nat) -> so (equal m n) -> eq m n.` | `equal` is sound |
| `equalRefl : (n : nat) -> so (equal n n).` | `equal` is reflexive |
| `lessIrrefl : (n : nat) -> so (less n n) -> empty.` | `less` is irreflexive |
| `plusZeroLeft : (n : nat) -> eq (plus 0 n) n.` | `0` is a left unit of `plus` |
| `plusSucLeft : (m n : nat) -> eq (plus (m + 1) n) (plus m n + 1).` | a successor on the left |
| `plusComm : (m n : nat) -> eq (plus m n) (plus n m).` | `plus` is commutative |
| `plusAssoc : (l m n : nat) -> eq (plus (plus l m) n) (plus l (plus m n)).` | `plus` is associative |
| `iequalSound : (a b : int) -> so (iequal a b) -> eq a b.` | `iequal` is sound |
| `iequalRefl : (a : int) -> so (iequal a a).` | `iequal` is reflexive |
| `iplusZero : (a : int) -> eq (a + 0) a.` | `0` is a unit of `+` |
| `inegNeg : (a : int) -> eq (-(-a)) a.` | negation is an involution |
| `iplusComm : (a b : int) -> eq (a + b) (b + a).` | `+` is commutative |
| `natEqual : decider { fst : nat, snd : nat } ([p] eq p.fst p.snd).` | a decider of equations of natural numbers |
| `intEqual : decider { fst : int, snd : int } ([p] eq p.fst p.snd).` | a decider of equations of integers |

## Proof by evaluation

`so` is defined by two clauses, `so true = unit.` and `so false = empty.`, with `unit`, its value `tt` and
the empty type `empty` of `std/eq`. A decider pairs a boolean check with a proof that the check is sound,
and `decide` applies the proof:

```hugin,ignore
decide = [d] [x] [t] d.sound x t.
```

For a closed value `x` whose check evaluates to `true`, the type `so (d.check x)` of the last argument
evaluates to `unit`, so `tt` is the proof: the elaborator checks the proposition by evaluating the check,
and the comparisons of `std/nat` and `std/int` evaluate in one native step each
([Native arithmetic](int.md#native-arithmetic)). For a value whose check evaluates to `false`, the last
argument would be a proof of `empty`, and `tt` is rejected ([E0901](../errors/E0901.md)). Nothing is
trusted beyond the evaluator: the soundness proof of the decider is an ordinary function, checked once.

The soundness lemmas split on the constructors, and the cases in which the check is `false` are absurd
clauses, since `so false` is the empty type:

```hugin,ignore
equalSound 0 0 T = refl.
equalSound 0 (N + 1) ().
equalSound (M + 1) 0 ().
equalSound (M + 1) (N + 1) T = cong suc (equalSound M N T).
iequalSound (ofNat M) (ofNat N) T = cong ofNat (equalSound M N T).
iequalSound (ofNat M) (negSucc N) ().
iequalSound (negSucc M) (ofNat N) ().
iequalSound (negSucc M) (negSucc N) T = cong negSucc (equalSound M N T).
```

The lemmas about `+` on integers follow the clauses of `iplus`: `iplusZero` holds by `refl` in each
case, and `iplusComm` uses `plusComm` where both integers are of the same sign.

## Examples

The following program defines the order of natural numbers as a family, a decider for it with a
soundness proof, and proves instances by `tt`, also on large numbers; it then decides equations of
integers.

```hugin,run
%use "std/eq" (eq, tt).
%use "std/nat" (less).
%use "std/decide".
lt : nat -> nat -> Type.
ltz : {n : nat} -> lt 0 (n + 1).
lts : {m n : nat} -> lt m n -> lt (m + 1) (n + 1).
lessSound : (m n : nat) -> so (less m n) -> lt m n.
lessSound M 0 ().
lessSound 0 (N + 1) T = ltz.
lessSound (M + 1) (N + 1) T = lts (lessSound M N T).
pair : Type = { fst : nat, snd : nat }.
ltDec : decider pair ([p] lt p.fst p.snd) = { check = [p] less p.fst p.snd, sound = [p] lessSound p.fst p.snd }.
big : lt 3 100000 = decide ltDec { fst = 3, snd = 100000 } tt.
negative : eq (3 - 10 * 2) (-17) = decide intEqual { fst = 3 - 10 * 2, snd = -17 } tt.
%opaque big negative.
proved : string -> rel.
proved "big".
```

```output
proved "big".
```

`less 3 100000` takes one native step, so `so (less 3 100000)` evaluates to `unit`. `lessSound M 0 ()` is
an absurd clause: `less M 0` evaluates to `false` by the first clause of `less`, and `so false` is the
empty type.

The following program uses the lemmas at variables.

```hugin,run
%use "std/eq" (eq, trans).
%use "std/decide".
twice : (a : int) -> eq (-(-(a + 0))) a = [a] trans (inegNeg (a + 0)) (iplusZero a).
swap : (a b : int) -> eq (a + b) (b + a) = iplusComm.
%opaque twice swap.
ok : int -> rel.
ok 1.
```

```output
ok 1.
```
