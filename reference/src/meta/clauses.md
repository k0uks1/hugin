# Clauses

A meta function can be defined by *clauses*: equations whose left sides are patterns over the function's
arguments. The clauses are compiled into a case tree that splits on the arguments' meta constructors
([Cockx and Abel 2018](../notation.md#references)). This chapter defines clauses, patterns and their
evaluation; [Coverage](coverage.md) and [Termination of meta functions](termination.md) define the
totality checks.

## Syntax

```text
Function  ::= NAME ":" Type "." Clause+
Clause    ::= NAME Pattern* ("=" Expr Where?)? "."
Pattern   ::= VAR | "_" | NAME | "(" NAME Pattern* ")" | INT | "(" Pattern "+" INT ")"
            | "(" Pattern ")" | "(" ")" | QuotedPattern
```

A function defined by clauses is declared first, `f : A.`, with a meta type `A`. Every item `f p₁ … pₙ =
e.` of the same file is then a clause of `f`, also when all its patterns are variables. The clauses may
be anywhere after or before the declaration; they are taken in the order in which they appear. A clause
may end with a [`where`](where.md) block. A [module body](../modules.md#module-bodies) is a scope for
clauses as a file is: the clauses of a function declared in a body are the items `f p̄ = e.` of that
body, and a clause in a body belongs to a function that the body declares.

A clause without `= e` is an *absurd clause*: its patterns contain the absurd pattern `()` (see below),
and it has no right-hand side. An item `f p̄.` whose patterns contain no `()` is not a clause but a fact
or an atom, as before. `()` is the two tokens `(` and `)`, with only whitespace or comments between them.

It is an error ([E0915](../errors/E0915.md)) if a function has clauses but no declaration (in a module
body: no declaration in that body), or if its clauses have different numbers of patterns or more patterns
than the function has explicit arguments. It is an error ([E0914](../errors/E0914.md)) to give clauses to
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
patterns of one clause. Implicit arguments are not written in patterns. The names of the implicit binders
of the function's declared type, such as `A` and `N` in `head : vec A (suc N) -> A`, are in scope in the
right-hand side, unless a pattern variable has the same name. Literals of `int`, `float` and `string` are
not patterns outside quoted patterns ([E0915](../errors/E0915.md)).

A literal pattern and a successor pattern are constructor patterns: [coverage](coverage.md) and
[termination](termination.md) see `suc (suc N)` for `N + 2`, so `N` is a constructor subterm of the
argument. It is an error ([E0915](../errors/E0915.md)) if the type of the argument is not nat-like, or if
a pattern with an operator is not a successor pattern: `N + 0`, `N + M` and `N - 1` are not patterns. A
pattern is matched one constructor at a time, so it is an error ([E0901](../errors/E0901.md)) if a
literal pattern or the `k` of a successor pattern is larger than 100000; numerals as values have no
such bound ([Inductive families](families.md#numerals)).

The following function is rejected: `N - 1` is not a pattern, since it is not built from constructors.

```hugin,compile_fail,E0915
pred : nat -> nat.
pred 0 = 0.
pred (N - 1) = N.
```

The patterns of a clause match the first arguments of the function, one per pattern. The right-hand side
is checked against the rest of the function's type, so a clause with fewer patterns than arguments
defines a function.

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
arguments before them, evaluates its *case tree* (Cockx and Abel 2018), the same tree as for
[coverage](coverage.md). The tree is defined by the clauses in their order: it keeps the clauses that may
still apply, and while the first of them has a constructor, literal or quoted pattern against an argument
that is not yet known, the tree *splits* on that argument. The argument split is the leftmost such
position of the first clause that may still apply: the first argument with one, and within an argument,
the outermost position first, then its constructor arguments from left to right (an absurd pattern `()`
comes after the clause's other patterns); a position whose split is undecided is passed over for the
clause's next one ([Undecided splits](coverage.md#undecided-splits)). A split has a branch per
constructor that can occur ([Index unification](coverage.md#index-unification)), in which the clauses
with another constructor there no longer apply. When the first clause that may still apply has no such
pattern left, its right-hand side gives the value. A numeral matches the constant of its family if it is
`0`, and the successor applied to its predecessor otherwise ([Inductive families](families.md#numerals)).
On arguments that are all known (closed constructor
applications), this is the first clause whose patterns match them. The arithmetic of
[`std/nat`](../std/nat.md#native-arithmetic) computes on numerals directly, with the value its clauses give,
and by its case tree on other arguments.

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
