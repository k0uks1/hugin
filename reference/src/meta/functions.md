# Functions and implicit arguments

Meta functions take meta values and object code to meta values and object code. This chapter defines
function types, lambdas and application, implicit arguments, the forms of definitions, and the literals
and primitive operations of the meta level. Functions defined by pattern matching are defined in
[Clauses](clauses.md).

## Function types

```text
PiType    ::= "(" NAME ":" Type ")" "->" Type      (dependent)
            | Type "->" Type                        (non-dependent)
            | "{" (VAR | NAME)+ ":" Type "}" "->" Type   (implicit)
```

`(x : A) -> B` is the type of functions that map an `x` of type `A` to a value of type `B`, where `B` may
mention `x`. `A -> B` is the case where it does not. `{x : A} -> B` is the type of functions whose
argument is *implicit*: it is not written at applications, and the compiler infers it. `{A B : Type} ->
C` binds two implicit arguments of the same type.

A function type whose result is `rel` is a relation type, and one whose domain and result are object
types is an object constructor type ([Declarations](../object/declarations.md#classification)). As a meta
type, `A -> B` with object types `A` and `B` checked against `Type` is the type of meta functions on
object code: `item -> prop` is the type of formula functions.

## Lambdas and application

```text
Lambda    ::= "[" (VAR | NAME) (":" Type)? "]" Expr
App       ::= Expr Expr
```

`[x] e` is the function that maps `x` to `e`; `[x : A] e` annotates the type of `x`. The body extends as
far to the right as possible. Application is juxtaposition and associates to the left: `f a b` is
`(f a) b`. It is an error ([E0905](../errors/E0905.md)) to apply a term that is not a function.

## Implicit arguments

At an application of a function with implicit arguments, the compiler inserts a fresh unknown for each
implicit argument and solves it by higher-order pattern unification with the types around it. An unknown
belongs to the item that creates it (see [the order of items](index.md)): it is solved within that item,
and later items cannot solve it. It is an error ([E0903](../errors/E0903.md)) if an implicit argument or
a type is not determined by the end of its item. Implicit arguments cannot be written explicitly; they
are inferred from the explicit arguments and the expected type.

Unification compares two terms up to their values: a definition is equal to its value, and an
application of a function defined by clauses that reduces is equal to its result. Two applications of
the same definition are first compared by their arguments, and by their values if the arguments differ.
An application of a function defined by clauses that does not reduce, because a split meets a variable
or an unknown, is compared with another application of the same function by its arguments, which may
solve an unknown that the function's result does not determine: with `c : nat -> nat` defined by
`c zero = zero.` and `c (suc N) = zero.`, an unknown *α* in the equation `c` *α* `= c Y` is solved as
*α* `:= Y`, although `c` ignores its argument.

In the following program the argument written `_` in `same` is determined only by comparing
`c` *α* with `c Y` by their arguments, which solves *α* `:= Y`.

```hugin,run
eqn : nat -> nat -> Type.
refl : eqn N N.
c : nat -> nat.
c zero = zero.
c (suc N) = zero.
pick : (x : nat) -> (y : nat) -> eqn (c x) (c y) -> nat.
pick X Y E = X.
same : nat -> nat.
same Y = pick _ Y refl.
size : nat -> int.
size zero = 0.
size (suc N) = size N + 1.
answer : int -> rel.
answer (size (same (suc (suc zero)))).
```

```output
answer 2.
```

The free uppercase variables of the type of a declaration `x : A.` or `x : A = e.` are implicit arguments
of `x`. So `ident : A -> A = [x] x.` declares `ident : {A : Type} -> A -> A`. The free uppercase
variables in the parameter types of a definition, `f (x : A) = e.` or `f (x : A) : B = e.`, and in its
result type are implicit arguments as well: `ident (x : A) : A = x.` declares
`ident : {A : Type} -> A -> A`. The type of such a variable is not given. The compiler tries it as a meta
type first, then as an object type.

The following program composes two functions on compile-time integers. `compose` has three implicit
arguments, which are inferred as `int` at its application.

```hugin,run
compose : {A B C : Type} -> (B -> C) -> (A -> B) -> A -> C = [g] [f] [x] g (f x).
inc (n : int) : int = n + 1.
double (n : int) : int = n * 2.
result : int -> rel.
result (compose inc double 20).
```

```output
result 41.
```

## Definitions

```text
Definition ::= NAME Param* (":" Type)? "=" Expr "."
```

A *definition* gives a constant a value. Its forms are:

- `x : A = e.`: `e` is checked against the type `A`;
- `x = e.`: the type of `x` is the inferred type of `e`;
- `f p₁ … pₙ = e.` and `f p₁ … pₙ : A = e.`: `f` is the function `[p₁] … [pₙ] e`; a parameter `(x : T)`
  has the type `T`, and a parameter `X` an inferred type (in a type definition `t X : type = τ.`, `X`
  ranges over object types).

A definition is a value: it is evaluated where it is used. Diagnostics, the language server and
`--print-after elaborate` show it by its name where a type or an implicit argument comes from it
(`w : vec2 = ident {vec2} v.` after `vec2 : Type = vec int two.` and `v : vec2`); conversion uses its
value. The binders of a declared type do not scope
over the definition. It is an error ([E0916](../errors/E0916.md)) to use them there:
`double : (x : int) -> int = x * 2.` is written `double (x : int) : int = x * 2.`, and `hugin fix` makes
this change.

After a declaration `f : A.`, an item `f X₁ … Xₙ = e.` is a [clause](clauses.md) of `f`, not a
definition.

## Typed holes

```text
Hole      ::= "?" | "?" NAME_CHARS
```

A *typed hole* `?` or `?name` stands for an expression that is still to be written. It is checked like
any expression: its type, the *goal*, is the type its position expects, and it is an unknown that the
rest of the item may constrain. Later items cannot constrain it: an item whose elaboration would need a
value for the hole of an earlier item is left out without a further diagnostic, since the hole is
reported. A hole may stand in meta code and in object code; in object code its goal is an object type,
such as the type of a column. Every hole is an error ([E0924](../errors/E0924.md)), whose diagnostic
reports the goal and the variables in scope. The items around a hole are still elaborated, so all holes
are reported at once; compilation stops before staging. A hole in an item that has another error is not
reported. The name of a hole only identifies it in messages. A hole is not object syntax: in the content
of a [quote](../reflection.md#quotes) it is an error ([E0917](../errors/E0917.md)).

The following program leaves the argument of the outer `suc` as a hole. The compiler reports its goal,
`nat`.

```hugin,compile_fail,E0924
double : nat -> nat.
double zero = zero.
double (suc N) = suc (suc ?).
```

The following rule leaves a column of its body as a hole. Its goal is the column's object type, `int`.

```hugin,compile_fail,E0924
edge : int -> int -> rel.
reach : int -> rel.
reach X :- edge X ?next.
```

In the following program the hole `?t` is the value of the type `t`. The definition `x` would need
`?t` to be `int`, but `?t` belongs to the item `t`: the compiler reports the hole, and leaves `x` out
without reporting it.

```hugin,compile_fail,E0924
t : Type = ?t.
x : t = 5.
```

> **Note.** Holes support writing a program step by step. The language server shows the goal of a hole,
> and offers to split cases and to add missing clauses, with holes for their right-hand sides.

## Literals and primitive operations

A literal checked against a meta type is a *meta value*: `3 : int` is a compile-time integer. An integer
literal checked against a type `A` is:

1. the numeral of `A`, if `A` is a nat-like family, such as `nat` with `zero` and `suc`
   ([Inductive families](families.md#numerals));
2. a literal of `A` at the stage of its position, if `A` is a base type;
3. if `A` is still an unknown, an unknown of type `A` that waits until the end of its item, or of the
   member of a module body that contains it. The literal is then checked against `A` as the item has
   determined it, by rule 1 or 2; if `A` is still unknown, it is `int` at stage 1. The waiting literals
   of an item are checked earlier where the item needs a value whose type is not known yet: before
   such a value is used as object code (a value of unknown type is object code only if checking them
   does not determine its type), and before it is reflected as syntax.

An integer literal operand of arithmetic other than `e + k` next to an operand of unknown type makes
that type `int` at once: `[x] x * 10` is a function on `int`.

So a literal takes its type from the rest of its item: with `pick : {A : Type} -> A -> A -> A`, both
`pick 3 zero` and `pick zero 3` are naturals, and `pick 3 4` is an `int`. A literal never becomes a
numeral by default. A literal that is not checked against a type, such as an operand whose type is
inferred, has its base type. A float or string literal has its base type.

The following program takes the type of each literal from the other argument of `pick`.

```hugin,run
%use "std/nat".
pick : {A : Type} -> A -> A -> A.
pick X _ = X.
a : nat = pick 3 zero.
b = pick 4 5.
shown : int -> rel.
shown (toInt a).
shown b.
```

```output
shown 3.
shown 4.
```

> **Rationale.** The default is `int`, not a nat-like type as in Agda or Lean, because most literals are
> object integers, and a default must not change the stage of a term: a nat-like type has no lifting to
> object code.

The arithmetic operators `+`, `-`, `*`, `/` and `^` apply to meta values of the base types as they do to
object values ([Arithmetic and comparisons](../object/arithmetic.md)); they are computed at compile time.
A literal operand takes the type and stage of the other operand. Comparisons are always object
formulas; the meta level has no comparison operators.

A meta value of a base type used as object code is *persisted* as a literal
([Staging](staging.md#lifting)). It is an error ([E0909](../errors/E0909.md)) if its computation is
undefined (an overflow, a division by zero) or stuck.

The following program computes a constant at compile time and uses it in object code.

```hugin,run
seconds_per_day : int = 24 * 60 * 60.
label : string = "day" ^ "s".
unit : string -> int -> rel.
unit label seconds_per_day.
```

```output
unit "days" 86400.
```
