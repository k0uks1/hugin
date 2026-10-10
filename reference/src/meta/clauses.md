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
Pattern   ::= VAR | "_" | NAME | "(" NAME Pattern* ")" | INT | "(" Pattern ")" | "(" ")" | QuotedPattern
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
- a [quoted pattern](../reflection.md#quoted-patterns), if the argument has a reflective type;
- the *absurd pattern* `()`, at a position none of whose constructors can occur (as in Agda), in an
  absurd clause.

Patterns are linear: it is an error ([E0915](../errors/E0915.md)) if a variable occurs twice in the
patterns of one clause. Implicit arguments are not written in patterns. The names of the implicit binders
of the function's declared type, such as `A` and `N` in `head : vec A (suc N) -> A`, are in scope in the
right-hand side, unless a pattern variable has the same name. Literals of `int`, `float` and `string` are
not patterns outside quoted patterns ([E0915](../errors/E0915.md)).

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
a right-hand side fails in its context but checks at every case of the [case tree](coverage.md#case-trees)
that uses the clause, the error has a fix that writes these cases as clauses (`w (suc _) X = X.`); the
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
arguments before them, evaluates its case tree. The first clause whose patterns match the arguments gives
the value. If a split is on an argument that is not yet a constructor application (a variable of an
enclosing function, a postulate), the application stays unevaluated until the argument is known.

Applications to closed arguments are memoised by their normal forms. Since meta functions are total and
have no effects, this does not change their values; it makes the evaluation of a function such as `fib`
below linear in its argument.

The following program computes a Fibonacci number at compile time with a function by clauses over a
meta type of natural numbers. The literal `90` is the numeral of `nat`.

```hugin,run
nat : Type.
zero : nat.
suc : nat -> nat.
fib : nat -> int.
fib zero = 0.
fib (suc zero) = 1.
fib (suc (suc N)) = fib N + fib (suc N).
fib90 : int -> rel.
fib90 (fib 90).
```

```output
fib90 2880067194370816120.
```

The following program defines addition by clauses with a variable pattern for the second argument.

```hugin,run
nat : Type.
zero : nat.
suc : nat -> nat.
plus : nat -> nat -> nat.
plus zero N = N.
plus (suc M) N = suc (plus M N).
toInt : nat -> int.
toInt zero = 0.
toInt (suc N) = toInt N + 1.
total : int -> rel.
total (toInt (plus 2 3)).
```

```output
total 5.
```
