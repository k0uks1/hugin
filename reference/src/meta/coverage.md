# Coverage

Meta functions are total. A function defined by clauses must have a clause for every combination of
arguments of its declared type. This chapter defines how the compiler checks this, taking the indices of
inductive families into account, and the warning for clauses that are never used.

## Case trees

The compiler translates the clauses of a function into a *case tree*, following [Cockx and Abel
2018](../notation.md#references) without copatterns. It keeps a list of the clauses that may still apply,
each with equations between the arguments and its patterns. While the first clause that may apply has a
constructor pattern against an argument that is not yet known, the tree *splits* on that argument: it
gets one branch per constructor of the argument's type. In each branch, the clauses whose pattern there
is another constructor no longer apply. When the first clause that may apply has no constructor patterns
left, its right-hand side is the leaf of the branch.

## Index unification

When the type of the argument is an indexed family, a constructor gets a branch only if its result type
unifies with the argument's type. Unification solves variables (`N := suc M`), decomposes constructor
applications, and detects conflicts (`zero` against `suc M`) and cycles (`N` against `suc N`). A
constructor whose indices conflict cannot occur, and needs no clause.

The following function takes the first element of a non-empty vector. `vnil` has length `zero`, which
conflicts with `suc N`, so `head` needs no clause for it.

```hugin,run
nat : Type.
zero : nat.
suc : nat -> nat.
vec : Type -> nat -> Type.
vnil : vec A zero.
vcons : A -> vec A N -> vec A (suc N).
head : vec A (suc N) -> A.
head (vcons X _) = X.
first : int -> rel.
first (head (vcons 7 (vcons 8 vnil))).
```

```output
first 7.
```

It is an error ([E0915](../errors/E0915.md)) if unification meets a problem that it can neither solve nor
refute, such as an index `plus N M` that is a stuck function application against `zero`.

## Missing cases

It is an error ([E0911](../errors/E0911.md)) if a branch of the case tree has no clause and some
constructor could occur in it. The diagnostic shows the missing pattern, as the clauses are written: a
local function of a [`where`](where.md) block or a member function of a
[module body](../modules.md#module-bodies) is shown without the variables of its context that it uses
(`f.g (suc _)` for a local function `g` of `f`). A branch without clauses is accepted if some argument in
it has a type without possible constructors.

The following function is rejected, since it has no clause for `zero`.

```hugin,compile_fail,E0911
nat : Type.
zero : nat.
suc : nat -> nat.
pred : nat -> nat.
pred (suc N) = N.
```

## Unreachable clauses

A clause that is not the leaf of any branch is *unreachable*: the clauses before it match everything it
matches. The compiler warns about it ([W0006](../errors/W0006.md), lint `unreachable_clauses`).

> **Note.** A clause is unreachable only if the clauses before it together match everything it matches.
> In `isZero zero = 1. isZero N = 0. isZero (suc N) = 0.` the third clause is unreachable, since the
> second matches every argument. The second clause is reachable, although the first matches one of its
> arguments.
