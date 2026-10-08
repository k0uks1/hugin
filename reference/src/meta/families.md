# Inductive families

An *inductive family* is a meta type defined by its *meta constructors*. It may be indexed by values:
`vec A N` is the type of vectors of length `N`. Inductive families are the data types of the meta level;
they exist only at compile time. This chapter defines their declaration and the checks on it.

## Syntax

```text
Family      ::= NAME ":" (Type "->")* "Type" "."
Constructor ::= NAME ":" (Type "->")* NAME Expr* "."
```

A meta declaration without a definition and without clauses is classified by its type:

- `T : Δ -> Type.`, whose type ends in a universe, declares an inductive family with the arguments `Δ`;
- `c : Δ -> T ū.`, whose type ends in a family `T` of the same file, declares a meta constructor of `T`;
- any other meta declaration declares a postulate ([The meta level](index.md#meta-items)).

The constructors of a family are the constructor declarations that return it, in the order of the file.
A constructor must return the family applied to all of its arguments; it is an error otherwise
([E0914](../errors/E0914.md), or [E0901](../errors/E0901.md) if the result is not a type). A program cannot add constructors to a family of the prelude or
of another file: `x : formula.` in a program declares a postulate.

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
argument, as in `tapp : sym -> seq term -> term` of the prelude. It is an error
([E0913](../errors/E0913.md)) otherwise.

```hugin,compile_fail,E0913
bad : Type.
mk : (bad -> int) -> bad.
```

> **Rationale.** A constructor such as `mk` allows a value that applies itself, and with it a
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
