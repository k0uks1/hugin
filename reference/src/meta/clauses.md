# Clauses

A meta function can be defined by *clauses*: equations whose left sides are patterns over the function's
arguments. The clauses are compiled into a case tree that splits on the arguments' meta constructors
([Cockx and Abel 2018](../notation.md#references)). This chapter defines clauses, patterns and their
evaluation; [Coverage](coverage.md) and [Termination of meta functions](termination.md) define the
totality checks.

## Syntax

```text
Function  ::= NAME ":" Type "." Clause*
Clause    ::= NAME (Pattern | ImplicitPattern)* ("=" Expr Where?)? "."
Pattern   ::= VAR | "_" | NAME | "(" NAME (Pattern | ImplicitPattern)* ")" | INT
            | "(" Pattern "+" INT ")" | "(" Pattern ")" | "(" ")" | QuotedPattern
ImplicitPattern ::= "{" (VAR | NAME) ":=" Pattern "}"
```

A function defined by clauses is declared first, `f : A.`, with a meta type `A`. Every item `f p₁ … pₙ =
e.` of the same file is then a clause of `f`, also when all its patterns are variables. A declaration
without clauses and without a value whose type does not make it an inductive family or a constructor
([Inductive families](families.md#syntax)) declares a function too, with no clauses. They must cover its
arguments as any clauses ([Coverage](coverage.md#missing-cases)): that holds only if one of its explicit
arguments has an empty type, so `boom : (A : Type) -> A.` is an error ([E0911](../errors/E0911.md)). A
constant without a value is declared as a [postulate](functions.md#postulates). The clauses may
be anywhere after or before the declaration; they are taken in the order in which they appear. A clause
may end with a [`where`](where.md) block. A case split on the right-hand side is a
[`match`](match.md), whose branches are the clauses of a local function. A [module body](../modules.md#module-bodies) is a scope for
clauses as a file is: the clauses of a function declared in a body are the items `f p̄ = e.` of that
body, and a clause in a body belongs to a function that the body declares.

A clause without `= e` is an *absurd clause*: its patterns contain the absurd pattern `()` (see below),
and it has no right-hand side. An item `f p̄.` whose patterns contain no `()` is not a clause but a fact
or an atom, as before. `()` is the two tokens `(` and `)`, with only whitespace or comments between them.

It is an error ([E0915](../errors/E0915.md)) if a function has clauses but no declaration (in a module
body: no declaration in that body), or if its clauses have different numbers of patterns or more patterns
than the function has explicit arguments. The [implicit patterns](#implicit-patterns) of a clause do not
count. It is an error ([E0914](../errors/E0914.md)) to give clauses to
a constant that is not a meta function, such as a relation or a constructor.

## Patterns

A *pattern* is one of:

- a variable `X`, which matches any value and binds `X` in the right-hand side;
- the wildcard `_`, which matches any value;
- a meta constructor applied to patterns for its explicit arguments, `suc N`, `(vcons X XS)`; a
  constructor without arguments is written as its name, `zero`;
- an integer literal, if the argument's type is nat-like ([Inductive families](families.md#numerals));
  `3` is the pattern `suc (suc (suc zero))`;
- a *successor pattern* `P + k`, where `P` is a pattern and `k` an integer literal of at least 1, if the
  argument's type is nat-like: the successor constructor applied `k` times to `P`; `N + 2` is the
  pattern `suc (suc N)`;
- a [quoted pattern](../reflection.md#quoted-patterns), if the argument has a reflective type;
- the *absurd pattern* `()`, at a position none of whose constructors can occur (as in Agda), in an
  absurd clause.

Patterns are linear: it is an error ([E0915](../errors/E0915.md)) if a variable occurs twice in the
patterns of one clause. An implicit argument is matched only by an [implicit
pattern](#implicit-patterns). The names of the implicit binders of the function's declared type, such as
`A` and `N` in `head : vec A (suc N) -> A`, are in scope in the right-hand side, unless a pattern
variable has the same name or an implicit pattern matches the binder. Literals of `int`, `float` and
`string` are not patterns outside quoted patterns ([E0915](../errors/E0915.md)).

A literal pattern and a successor pattern stand for constructor patterns: `3` for `suc (suc (suc
zero))` and `N + 2` for `suc (suc N)`, so [coverage](coverage.md) and [termination](termination.md) see
`N` as a constructor subterm of the argument. Against a nat-like family, every pattern is read as a
*numeral pattern*: a literal `k` (also `zero`, and the successor applied to a literal), or a pattern `P`
with the successor applied `j` times, `P + j` (also `suc P`; `P` itself if `j = 0`). Literal and
successor patterns have no upper bound. It is an error ([E0915](../errors/E0915.md)) if the type of the
argument is not nat-like, or if a pattern with an operator is not a successor pattern: `N + 0`, `N + M`
and `N - 1` are not patterns.

The following function is rejected: `N - 1` is not a pattern, since it is not built from constructors.

```hugin,compile_fail,E0915
pred : nat -> nat.
pred 0 = 0.
pred (N - 1) = N.
```

The patterns of a clause match the first arguments of the function, one per pattern. The right-hand side
is checked against the rest of the function's type, so a clause with fewer patterns than arguments
defines a function.

## Implicit patterns

An *implicit pattern* `{x := p}` matches the implicit argument whose binder is named `x` with the pattern
`p`; `:=` is written as in an [implicit argument by name](functions.md#implicit-arguments-by-name). It is
one of the following:

- among the patterns of a clause, a pattern for an implicit argument of the function: one of the implicit
  binders of its type before the first explicit binder after the clause's explicit patterns, so
  `size {n := N} = N.` matches the only argument of `size : {n : nat} -> nat`;
- in a constructor pattern, a pattern for an implicit argument of the constructor: `vcons {N := K} X Xs`
  binds the length `K` of `Xs`, which `vcons : A -> vec A N -> vec A (N + 1)` does not take explicitly.

Implicit patterns may be written anywhere among the explicit patterns; they are matched by name, not by
position. An implicit argument is matched like an explicit one: a variable binds it, and a constructor or
numeral pattern splits on it ([Evaluation](#evaluation)). An implicit argument of a constructor is often
determined by [index unification](coverage.md#index-unification): a pattern variable then binds the value
it determined. It is an error ([E0926](../errors/E0926.md)) if no implicit binder of that name can be
matched there, and ([E0915](../errors/E0915.md)) if a clause or a constructor pattern matches the same
binder twice. A missing case shows an implicit argument that a clause matches by name where the case
constrains it: `isEmpty {n := _ + 1} _`.

The following program reads the length of a vector from the function's implicit argument, and the
length of its tail from the implicit argument of `vcons`.

```hugin,run
vec : Type -> nat -> Type.
vnil : vec A 0.
vcons : A -> vec A N -> vec A (N + 1).
toInt : nat -> int.
toInt 0 = 0.
toInt (N + 1) = toInt N + 1.
length : {A : Type} -> {n : nat} -> vec A n -> nat.
length {n := N} V = N.
tailLength : {A : Type} -> {n : nat} -> vec A n -> nat.
tailLength vnil = 0.
tailLength (vcons {N := K} X Xs) = K.
sizes : int -> int -> rel.
sizes (toInt (length (vcons 1 (vcons 2 vnil)))) (toInt (tailLength (vcons 1 (vcons 2 vnil)))).
```

```output
sizes 2 1.
```

## Checking a clause

Each clause is checked on its own, once, as in Agda, Idris 2 and Lean 4. Its *clause context* is
obtained by splitting the function's arguments by that clause's patterns alone, with the [index
unification](coverage.md#index-unification) of coverage: one variable per variable or wildcard of the
patterns and per argument of a matched constructor that a pattern does not name, with the solutions that
index unification finds. The right-hand side, the [`where`](where.md) block and the recursive calls for
the [termination check](termination.md) are checked in the clause context, in which the pattern
variables are bound, and the names of the implicit binders of the function's declared type are in scope
unless a pattern variable has the same name.

The clauses before a clause do not refine its context: in

```text
w : (n : nat) -> sel (isz n) -> bool.
w zero X = true.
w N X = X.
```

the second clause is checked with `N` a variable, so `X` has type `sel (isz N)`, not `bool`, and the
clause is rejected ([E0901](../errors/E0901.md)), although every argument it is used for is `suc _`. If
a right-hand side fails in its context but checks at every case of the [case tree](#evaluation)
that uses the clause, the error has a fix that writes these cases as clauses (`w (_ + 1) X = X.`); the
same holds for a call that decreases only in those cases ([E0912](../errors/E0912.md)). A clause that is
never used ([W0006](../errors/W0006.md)) is checked as well.

It is an error ([E0915](../errors/E0915.md)) if a constructor of a clause's own patterns cannot occur in
its context: no argument can match the clause. In `k zero (vcons X XS) = zero.` for `k : (n : nat) ->
vec bool n -> nat`, the index `suc _` of `vcons` conflicts with `zero`. The fix removes the clause, or, if
it is the function's only clause and no constructor can occur at the position, replaces the pattern by
`()`.

An absurd pattern `()` must be at a position whose type, in the clause context, has no constructor that
can occur: index unification must end in a conflict for every constructor. It is an error
([E0915](../errors/E0915.md)) otherwise, and also if an absurd clause has a right-hand side, or if `()`
is used anywhere but in the patterns of a clause. An absurd clause matches no argument: it is never the
clause that gives a function's value, and it is never unreachable. It states that the cases it stands for
are impossible; where coverage finds that by itself (a variable of an empty type, as in
[Missing cases](coverage.md#missing-cases)), the absurd clause may be left out.

The following function on `fin zero`, the empty type of numbers below zero, needs only an absurd clause;
`last` uses `()` inside a constructor pattern.

```hugin,run
nat : Type.
zero : nat.
suc : nat -> nat.
fin : nat -> Type.
fzero : fin (suc N).
fsuc : fin N -> fin (suc N).
vec : Type -> nat -> Type.
vnil : vec A zero.
vcons : A -> vec A N -> vec A (suc N).
none : fin zero -> int.
none ().
last : vec (fin zero) (suc zero) -> int.
last (vcons () _).
size : vec int N -> int.
size vnil = 0.
size (vcons _ XS) = size XS + 1.
total : int -> rel.
total (size (vcons 1 (vcons 2 vnil))).
```

```output
total 2.
```

## Evaluation

An application of a function to as many arguments as its clauses have patterns, with the implicit
arguments before them and those that its implicit patterns match, evaluates its *case tree* (Cockx and
Abel 2018), the same tree as for [coverage](coverage.md). The tree is defined by the clauses in their
order: it keeps the clauses that may still apply, and while the first of them has a constructor, literal
or quoted pattern against an argument that is not yet known, the tree *splits* on that argument. The
argument split is the leftmost such position of the first clause that may still apply: the first argument
with one, and within an argument, the outermost position first, then its constructor arguments from left
to right (an absurd pattern `()` comes after the clause's other patterns); a position whose split is
undecided is passed over for the clause's next one ([Undecided splits](coverage.md#undecided-splits)). A
split has a branch per constructor that can occur ([Index unification](coverage.md#index-unification)),
in which the clauses with another constructor there no longer apply. At an argument of a nat-like family,
where the patterns are numeral patterns, the split is *by value*, as Agda's literal branches and Lean's
value splits: a branch per literal that a clause that may still apply has there; then, if one of them has
`P + j` there, a branch for the values of at least the least such `j` (the argument is `Q + j` for a new
variable `Q`) and one for the other values below it; otherwise one for every other value. The clauses
with a literal do not apply in the branches that are not their value's, and those with `P + j` not in the
branch below `j`. When the first clause that may still apply has no such pattern left, its right-hand
side gives the value. A numeral matches the constant of its family if it is `0`, and the successor
applied to its predecessor otherwise ([Inductive families](families.md#numerals));
`f 50000 = 1. f _ = 0.` tests `50000` once, whatever its size. On arguments that are all known (closed
constructor applications), this is the first clause whose patterns match them. The arithmetic of
[`std/nat`](../std/nat.md#native-arithmetic) computes on numerals directly, with the value its clauses
give, and by its case tree on other arguments.

An application whose tree splits on an argument that is not a constructor application (a variable of an
enclosing function or of a clause, a postulate, a stuck application) stays unevaluated until the argument
is known, even if every clause that can match gives the same value. With

```text
gg : nat -> nat -> bool.
gg zero zero = true.
gg _ (suc _) = false.
gg (suc _) zero = true.
```

the first clause makes the tree split on the first argument, so `gg X (suc zero)` does not evaluate for a
variable `X`, and a type that mentions it is not `bool` ([E0901](../errors/E0901.md)). With the clause
`gg _ (suc _)` first, the tree splits on the second argument first, and `gg X (suc zero)` evaluates to
`false`. The split order is part of the language because it decides which applications evaluate, and so
which programs type-check; other column choices ([Maranget 2008](../notation.md#references)) would give
the same values on known arguments but not on unknown ones.

A clause *holds definitionally* if the tree uses it for exactly one case and that case is the clause's
own patterns (its [clause context](#checking-a-clause)): then every application that matches its
patterns evaluates by it. In the example the second clause does not: the tree uses it for `gg zero (suc
_)` and `gg (suc _) (suc _)`. A catch-all clause after a more specific one, such as `n2 _ _ = false.` after
`n2 zero zero = true.`, does not hold definitionally either. The compiler warns about such clauses
([W0009](../errors/W0009.md), lint `inexact_clauses`) only if the lint is turned on (`-W
inexact_clauses`): it is off by default, as Agda's `--exact-split`. It does not apply to the clauses of
the bundled library.

Applications to closed arguments are memoised by their normal forms. Since meta functions are total and
have no effects, this does not change their values; it makes the evaluation of a function such as `fib`
below linear in its argument.

The following program computes a Fibonacci number at compile time with a function by clauses over the
prelude's natural numbers. The literal `90` is the numeral of `nat`, and `N + 2` a successor pattern.

```hugin,run
fib : nat -> int.
fib 0 = 0.
fib 1 = 1.
fib (N + 2) = fib N + fib (N + 1).
fib90 : int -> rel.
fib90 (fib 90).
```

```output
fib90 2880067194370816120.
```

The following program defines addition by clauses with a variable pattern for the second argument.

```hugin,run
plus : nat -> nat -> nat.
plus 0 N = N.
plus (M + 1) N = plus M N + 1.
toInt : nat -> int.
toInt 0 = 0.
toInt (N + 1) = toInt N + 1.
total : int -> rel.
total (toInt (plus 2 3)).
```

```output
total 5.
```
