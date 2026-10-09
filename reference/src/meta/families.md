# Inductive families

An *inductive family* is a meta type defined by its *meta constructors*. It may be indexed by values:
`vec A N` is the type of vectors of length `N`. Inductive families are the data types of the meta level;
they exist only at compile time. This chapter defines their declaration and the checks on it, and the
[shared data types](#shared-data), which exist at both stages.

## Syntax

```text
Family      ::= NAME ":" (Type "->")* "Type" "."
Constructor ::= NAME ":" (Type "->")* NAME Expr* "."
```

A meta declaration without a definition and without clauses is classified by its type:

- `T : Δ -> Type.`, whose type ends in a universe, declares an inductive family with the arguments `Δ`;
- `c : Δ -> T ū.`, whose type ends in a family `T` of the same file, declares a meta constructor of `T`;
- any other meta declaration declares a postulate ([The meta level](index.md#meta-items)).

The constructors of a family are the constructor declarations that return it, in the order of the file. A
constructor must return the family applied to all of its arguments. It is an error otherwise
([E0914](../errors/E0914.md), or [E0901](../errors/E0901.md) if the result is not a type). A program
cannot add constructors to a family of the standard library or of another file: `x : formula.` in a
program declares a postulate.

Free uppercase variables in the type of a constructor are implicit arguments
([Functions](functions.md#implicit-arguments)): `vcons : A -> vec A N -> vec A (suc N).` has the implicit
arguments `A` and `N`. All arguments of a family are indices: pattern matching unifies them, and there is
no separate notion of parameters.

The following program declares the natural numbers and vectors indexed by their length, and appends
two vectors. The type of `append` states the length of the result.

```hugin,run
nat : Type.
zero : nat.
suc : nat -> nat.
plus : nat -> nat -> nat.
plus zero N = N.
plus (suc M) N = suc (plus M N).
vec : Type -> nat -> Type.
vnil : vec A zero.
vcons : A -> vec A N -> vec A (suc N).
append : vec A N -> vec A M -> vec A (plus N M).
append vnil YS = YS.
append (vcons X XS) YS = vcons X (append XS YS).
sumAll : vec int N -> int.
sumAll vnil = 0.
sumAll (vcons X XS) = X + sumAll XS.
total : int -> rel.
total (sumAll (append (vcons 1 (vcons 2 vnil)) (vcons 39 vnil))).
```

```output
total 42.
```

## Strict positivity

A family may occur in the argument types of its constructors only *strictly positively*: not to the left
of an arrow. It may occur in an argument of another family if that family is strictly positive in that
argument, as in `tapp : sym -> list term -> term` of `std/reflect`. It is an error
([E0913](../errors/E0913.md)) otherwise.

The following declaration is rejected: `lam` takes a function from `value` as its argument, so `value`
occurs to the left of an arrow.

```hugin,compile_fail,E0913
value : Type.
lam : (value -> value) -> value.
```

> **Rationale.** A constructor such as `lam` allows a value that applies itself, and with it a
> non-terminating computation without recursion.

## Universe levels

The argument types of a constructor must live in the universe of its family. The compiler turns this
into constraints on the levels ([Universes](universes.md)): `small : Type. mk : Type -> small.` puts
`small` into `Type₁`. An implicit argument of a constructor that is also an argument of its result type,
such as `A` in `vcons`, does not count.

## Numerals

A family is *nat-like* if it has exactly two constructors, one without arguments and one with a single
argument of the family itself, such as `zero : nat` and `suc : nat -> nat`. An integer literal `n`
checked against a nat-like family is the numeral `suc (… (suc zero))` with `n` applications, also in
patterns. The meta type `int` has no conversion to a nat-like family; a function by clauses converts in
the other direction.

## Shared data

A *shared data type* is a type that exists at both stages: a meta inductive family and a
[family](../object/types.md#families) of object constants, declared once under one name. It is declared
with the sort `data`, and its constructors are declared by their result type, as the constructors of a
family are.

```text
Shared ::= NAME VAR* ":" "data" "."
```

`data` is a keyword only as the whole type of a declaration. The `list` and `option` of the
standard library are shared data types ([`std/reflect`](../std/reflect.md#lists-options-and-booleans)).

### Restrictions

A shared data type `T a₁ … aₙ` is a family of first-order types in its parameters, so that both stages
can represent it.

- Every argument of a constructor of `T` has a *shareable* type: a parameter `aᵢ`, a base type, or a
  shared type applied to shareable types. It is an error ([E0920](../errors/E0920.md)) otherwise, for
  example for a function type, a universe, object code `⇑A`, `sym`, a relation, a meta type, or an object
  type that is not shared. Arguments may be labelled; the labels are column labels at the object level.
- Every constructor returns `T a₁ … aₙ` at its parameters, and every argument mentions `T` only at
  `a₁ … aₙ`: there are no indices and no polymorphic recursion. It is an error
  ([E0921](../errors/E0921.md)) otherwise, and if a parameter of the declaration is not a variable.
- A shared data type is closed. It is an error ([E0922](../errors/E0922.md)) if a subtyping edge
  `τ <: T` or a refinement `a : type <: T` names it, and an error ([E0923](../errors/E0923.md)) if a
  constructor of it is declared in another file. A program cannot add constructors to `list` or `option`.
- It is an error ([E0923](../errors/E0923.md)) if a shared data type is declared in a module body or in
  a [`where`](where.md) block.

The following declaration is rejected: the argument of `dots` has the meta type `nat`, which has no
object counterpart.

```hugin,compile_fail,E0920
nat : Type.
zero : nat.
shape : data.
dots : (amount : nat) -> shape.
```

### What a declaration declares

The declaration of `T` with the constructors `cᵢ : σ̄ᵢ -> T ā` declares, under the names `T` and `cᵢ`,

- the meta inductive family `T : Type -> … -> Type` with the meta constructors `cᵢ : σ̄ᵢ -> T ā`;
- the object family `T` of object constants, an object type if `T` has no parameters, with the
  constructors `cᵢ`, whose terms are facts ([Facts and identity](../object/facts.md));

and two meta functions, defined by one clause per constructor:

```text
T.lift  : (a₁ -> ⇑b₁) -> … -> (aₙ -> ⇑bₙ) -> T a₁ … aₙ -> ⇑(T b₁ … bₙ)
T.reify : (a₁ -> term) -> … -> (aₙ -> term) -> T a₁ … aₙ -> term
```

`T.lift f̄ (cᵢ x̄)` is the object term `cᵢ` applied to the arguments `x̄`, each turned into object code:
by `fⱼ` for a parameter `aⱼ`, as a literal for a base type, by the `lift` of its type for a shared type.
`T.reify ḡ (cᵢ x̄)` is the [term data](../reflection.md#the-reflective-types) of the same object term,
`'( cᵢ $(…) … )`. `T.reify` exists where the reflective types of `std/reflect` are part of the
compilation. Both are checked for coverage and termination like functions written by hand. Stage
inference inserts them ([Staging](staging.md#lifting), [Reflection](../reflection.md#holes)); a program
names them only to pass them as arguments, as `list.lift`.

> **Note.** An argument whose type nests the declared type in another shared type, such as
> `node : list (tree A) -> tree A`, is converted by an auxiliary function `tree.lift.1` (`tree.reify.1`),
> the fold of `list` at `tree A`, which calls `tree.lift` directly. Passing `tree.lift` to `list.lift`
> would hide the recursive call from the termination check.

### Names and stages

A name declared by a shared data declaration denotes the constant at the stage of its position
([The meta level](index.md#stages)): the object constant in a rule, a query, an object type, under `⇑`
and inside a quote `'( … )`; the meta constant in a clause, a meta type, a definition and in the
arguments of a directive outside quotes. In a declared type whose stage is inferred, the position has
the stage of the declared constant's result: `wrap : list int -> box.`, where `box` is an object type,
declares an object constructor with an object list column, and `size : list int -> int.` a meta
function. The parameters of a [formula function](staging.md#formula-functions) are object code, so a
shared type there is the object type. The list syntax `[a, b]` and `x :: xs` denotes `nil` and `cons` of
`list` at the stage of its position.

The following program computes a shape at compile time and uses the same constructors in a rule. The
fact `drawn (grow (circle 1))` is the lifted value `circle 2`.

```hugin,run
shape : data.
circle : (radius : int) -> shape.
square : (side : int) -> shape.
grow : shape -> shape.
grow (circle R) = circle (R + 1).
grow (square S) = square (S * 2).
drawn : shape -> rel.
drawn (grow (circle 1)).
drawn (square 3).
round : (radius : int) -> rel.
round R :- drawn (circle R).
?- round R.
```

```output
?- round R.
R = 2.
```

> **Rationale.** A shared type is a polynomial functor in its parameters. Its meta side is the initial
> algebra, the object constructors form an algebra on `⇑(T b̄)`, and `T.lift` is the fold between them.
> Everything a declaration generates can be written by hand, so it adds no rule to the core calculus. A
> lifted value is a closed object term: in a head it derives the fact and its nested facts, in a body it
> is an existence check, as the same term written by hand.
