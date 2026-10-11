# Clauses

A meta function can be defined by *clauses*: equations whose left sides are patterns over the function's
arguments. The clauses are compiled into a case tree that splits on the arguments' meta constructors
([Cockx and Abel 2018](../notation.md#references)). This chapter defines clauses, patterns and their
evaluation; [Coverage](coverage.md) and [Termination of meta functions](termination.md) define the
totality checks.

## Syntax

```text
Function  ::= NAME ":" Type "." Clause+
Clause    ::= NAME Pattern* "=" Expr Where? "."
Pattern   ::= VAR | "_" | NAME | "(" NAME Pattern* ")" | INT | "(" Pattern "+" INT ")"
            | "(" Pattern ")" | QuotedPattern
```

A function defined by clauses is declared first, `f : A.`, with a meta type `A`. Every item `f p₁ … pₙ =
e.` of the same file is then a clause of `f`, also when all its patterns are variables. The clauses may
be anywhere after or before the declaration; they are taken in the order in which they appear. A clause
may end with a [`where`](where.md) block. A [module body](../modules.md#module-bodies) is a scope for
clauses as a file is: the clauses of a function declared in a body are the items `f p̄ = e.` of that
body, and a clause in a body belongs to a function that the body declares.

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
- a [quoted pattern](../reflection.md#quoted-patterns), if the argument has a reflective type.

Patterns are linear: it is an error ([E0915](../errors/E0915.md)) if a variable occurs twice in the
patterns of one clause. Implicit arguments are not written in patterns. The names of the implicit binders
of the function's declared type, such as `A` and `N` in `head : vec A (suc N) -> A`, are in scope in the
right-hand side, unless a pattern variable has the same name. Literals of `int`, `float` and `string` are
not patterns outside quoted patterns ([E0915](../errors/E0915.md)).

A literal pattern and a successor pattern are constructor patterns: [coverage](coverage.md) and
[termination](termination.md) see `suc (suc N)` for `N + 2`, so `N` is a constructor subterm of the
argument. It is an error ([E0915](../errors/E0915.md)) if the type of the argument is not nat-like, or if
a pattern with an operator is not a successor pattern: `N + 0`, `N + M` and `N - 1` are not patterns. It
is an error ([E0901](../errors/E0901.md)) if `k` is larger than 100000.

The following function is rejected: `N - 1` is not a pattern, since it is not built from constructors.

```hugin,compile_fail,E0915
pred : nat -> nat.
pred 0 = 0.
pred (N - 1) = N.
```

The patterns of a clause match the first arguments of the function, one per pattern. The right-hand side
is checked against the rest of the function's type, so a clause with fewer patterns than arguments
defines a function.

## Evaluation

An application of a function to as many arguments as its clauses have patterns, with the implicit
arguments before them, evaluates its case tree. The first clause whose patterns match the arguments gives
the value. If a split is on an argument that is not yet a constructor application (a variable of an
enclosing function, a postulate), the application stays unevaluated until the argument is known.

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
