# Coverage

Meta functions are total. A function defined by clauses must have a clause for every combination of
arguments of its declared type. This chapter defines when the clauses cover these arguments and when a
clause is never used, taking the indices of inductive families into account. Both are defined on the
values the arguments can have (*probes*), as in [Maranget 2007](../notation.md#references), and do not
depend on the order in which the compiler inspects the arguments.

## Case trees

The compiler translates the clauses of a function into a *case tree*, following [Cockx and Abel
2018](../notation.md#references) without copatterns. It keeps a list of the clauses that may still apply,
each with equations between the arguments and its patterns. While the first clause that may apply has a
constructor pattern against an argument that is not yet known, the tree *splits* on that argument: it
gets one branch per constructor of the argument's type. In each branch, the clauses whose pattern there
is another constructor no longer apply. When the first clause that may apply has no constructor patterns
left, it is the leaf of the branch: its right-hand side, checked once in its [clause
context](clauses.md#checking-a-clause), at the arguments of the branch.

The tree splits in the *canonical order*: on the leftmost constructor position (by argument, then depth
first) of the first clause that may apply whose split is decided (see [Undecided
splits](#undecided-splits)). This is the order of Agda and Lean 4. The same tree evaluates applications
of the function: [Evaluation](clauses.md#evaluation) says when an application is stuck.

## Cases and probes

A *position* is a path to a subterm of the arguments: an argument, then the explicit arguments of the
constructors on the way. *Π* is the set of positions at which some clause has a constructor, a literal,
an atom of a quoted pattern or an absurd pattern `()`.

A *case* is a list of patterns for the arguments, with a variable for each wildcard. *Splitting* a case at
a variable of an inductive family gives one case per constructor of the type whose indices unify with the
variable's type ([Index unification](#index-unification)); the variable is *empty* if no constructor
can occur. A *probe* is a case obtained from the arguments as variables by splitting at positions of Π
until no variable at a position of Π can be split: each such variable is empty, or its split is
undecided. A probe is *refuted* if one of its variables is empty: no value matches it.

A clause *matches* a probe if the probe is an instance of the clause's patterns. A clause with a
constructor at a position where the probe has an empty variable does not match it; an absurd clause
matches no probe.

- A clause is *reachable* if some probe is matched by it and by no clause before it. Otherwise it is
  *unreachable* ([Unreachable clauses](#unreachable-clauses)).
- A probe is *missing* if no clause matches it and it is not refuted. The clauses *cover* the function if
  no probe is missing ([Missing cases](#missing-cases)).

These definitions do not depend on the order of the splits, nor on the case tree. The compiler reads
them off its tree, which splits at positions of Π: a clause is reachable exactly if it is a leaf of the
tree, where the analysis goes on below an empty variable with the clauses that have no constructor
there, and the missing probes are those below the branches without clauses.

At a position of a nat-like family, where the patterns are numeral patterns
([Clauses](clauses.md#patterns)), the probes are *value classes* instead of unary terms: the literals `k`
and offsets `P + j` of the clauses at the position cut the numerals into the singletons `{k}` and the
intervals between the cuts `k`, `k + 1` and `j`, the last one unbounded, and no clause tells the numerals
of a class apart. A singleton or a bounded interval gives a probe per numeral in it, and the unbounded
interval from `a` the probe `Q + a` (`Q` if `a` is 0). These are the verdicts of the unary probes `sucⁿ
zero`, at the cost of the number of literals and offsets, not of their values: `f 3 = 0. f (N + 5) = 1.`
misses `f 0`, `f 1`, `f 2` and `f 4`.

Emptiness is decided one level deep: a variable is empty if every constructor of its type conflicts with
its indices. A refuted probe needs no clause, but a clause that matches only refuted probes is
reachable. In the following program, `none` is a legitimate function on `fin 0`, the empty type of
numbers below zero, although no argument can reach its clause; `pick` needs no clause for `no`, since
its second argument would have the empty type `fin 0`.

```hugin,run
fin : nat -> Type.
fzero : fin (N + 1).
fsuc : fin N -> fin (N + 1).
two : Type.
yes : two.
no : two.
none : fin 0 -> int.
none X = 0.
pick : two -> fin 0 -> int.
pick yes X = 1.
answer : int -> rel.
answer 42.
```

```output
answer 42.
```

## Index unification

When the type of the argument is an indexed family, a constructor gets a branch only if its result type
unifies with the argument's type. Unification solves variables (`N := suc M`), decomposes constructor
applications, and detects conflicts (`zero` against `suc M`) and cycles (`N` against `suc N`). A
constructor whose indices conflict cannot occur, and needs no clause.

The following function takes the first element of a non-empty vector. `vnil` has length `zero`, which
conflicts with `suc N`, so `head` needs no clause for it.

```hugin,run
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

An equation that unification can neither solve nor refute yet, such as an index `double N` (a stuck
function application) against `0`, is *postponed* until the other equations make no more progress, as
in Agda's unifier: a later equation may solve `N`, after which `double N` reduces. Unification is
*stuck* if a whole round of the postponed equations solves nothing.

## Undecided splits

A split whose index unification is stuck for some constructor is *undecided*. The tree then tries the
next constructor position of the same clause (Agda's `altM1`), in the canonical order. It is an error
([E0915](../errors/E0915.md)) if every constructor position of the first clause that may apply is
undecided, or if a constructor pattern meets an argument that unification determined to be neither a
constructor application nor a variable. A clause's own context ([Checking a
clause](clauses.md#checking-a-clause)) is split in the same order.

In the following function, the type of the vector depends on the implicit `n` through `double n`, which
is stuck. The tree splits on the equality proof first, which solves `n`; then `vnil` is decided.

```hugin,run
double : nat -> nat.
double 0 = 0.
double (N + 1) = double N + 2.
vec : Type -> nat -> Type.
vnil : vec A 0.
vcons : A -> vec A N -> vec A (N + 1).
same : nat -> nat -> Type.
refl : same N N.
empty : {n : nat} -> vec int (double n) -> same n 0 -> int.
empty vnil refl = 0.
ok : int -> rel.
ok 1.
```

```output
ok 1.
```

With the clause `d N vnil = …` for `d : (n : nat) -> vec int (double n) -> int`, the only constructor
position of the clause is undecided (`0 = double n`): the clause is rejected, as in Agda, although
splitting `n` first would decide it.

A clause whose own constructors cannot occur, such as a `vnil` clause for `head`, is an error
([E0915](../errors/E0915.md), [Checking a clause](clauses.md#checking-a-clause)).

## Absurd clauses

An [absurd clause](clauses.md#checking-a-clause) `f p̄.` takes part in the case tree like any clause, but
an absurd pattern `()` splits only when the clause has no other constructor pattern left, and every
branch of that split drops the clause: its variable's type has no possible constructor, so the split has
no branches. An absurd clause is never a leaf, and never unreachable.

## Missing cases

It is an error ([E0911](../errors/E0911.md)) if the clauses do not cover the function. The diagnostic
shows the *most general missing patterns* `M`: the patterns `q` such that no clause matches a probe below
`q`, some probe below `q` is missing, and no generalization of `q` (a subpattern replaced by `_`) has
both properties. Whether a clause matches a probe below `q` is decided pairwise: the clause's patterns
and `q` clash at a constructor, or their common instance has a conflict in its indices. `M` is sorted
argument by argument, with `_` first and constructors in declaration order. The diagnostic shows the
first pattern of `M` and the number of the others; the editor's "add missing clauses" adds a clause for
each pattern of `M` in this order, leaving out a pattern whose missing probes the patterns before it
cover, and at most 20.

For `f 0 0 = 0.`, `M` is `f _ (_ + 1)` and `f (_ + 1) _`: the diagnostic shows `f _ (_ + 1)` and "1
more". For `big 3 = 0.`, it is `big 0`, `big 1`, `big 2` and `big (_ + 4)`. The patterns are shown as the
clauses are written: a local function of a [`where`](where.md) block or a member function of a
[module body](../modules.md#module-bodies) is shown without the variables of its context that it uses
(`f.g (_ + 1)` for a local function `g` of `f`). Implicit arguments are not shown.

A function declared without clauses ([Clauses](clauses.md#syntax)) is checked as a function whose
clauses have a variable pattern for each explicit argument: no clause matches any probe, so it is covered
only if an explicit argument has an empty type, and otherwise `M` is the pattern `f _ … _`. So
`absurd : empty -> nat.` (with a family `empty` without constructors) needs no clause, and
`boom : (A : Type) -> A.` is rejected with `boom _` missing.

```hugin,compile_fail,E0911
boom : (A : Type) -> A.
```

Literal and successor patterns of a nat-like type are constructor patterns
([Clauses](clauses.md#patterns)): `0` is `zero` and `N + 1` is `suc N`, so the clauses `f 0 = …` and
`f (N + 1) = …` cover `nat`. A missing case of a nat-like type is shown with numerals: `f 0`, `f (_ + 1)`.

The following function is rejected, since it has no clause for `0`.

```hugin,compile_fail,E0911
pred : nat -> nat.
pred (N + 1) = N.
```

The following function covers `nat` with a literal pattern, a successor pattern of a literal and a
successor pattern of a variable.

```hugin,run
parity : nat -> string.
parity 0 = "even".
parity 1 = "odd".
parity (N + 2) = parity N.
shown : string -> rel.
shown (parity 7).
```

```output
shown "odd".
```

## Unreachable clauses

A clause that is not reachable is *unreachable*: the clauses before it match every probe it matches. The
compiler warns about it ([W0006](../errors/W0006.md), lint `unreachable_clauses`). An absurd clause is
never unreachable, and a clause whose own constructors cannot occur is an error instead
([E0915](../errors/E0915.md)).

> **Note.** A clause is unreachable only if the clauses before it together match everything it matches.
> In `isZero 0 = 1. isZero N = 0. isZero (N + 1) = 0.` the third clause is unreachable, since the
> second matches every argument. The second clause is reachable, although the first matches one of its
> arguments.
