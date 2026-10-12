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
a type is not determined by the end of its item. An implicit argument is inferred from the explicit
arguments and the expected type, unless it is given by name ([below](#implicit-arguments-by-name)).

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
size 0 = 0.
size (N + 1) = size N + 1.
answer : int -> rel.
answer (size (same 2)).
```

```output
answer 2.
```

An application of a meta constant, a constructor, function, definition or postulate, checked against an
expected type, `f a₁ … aₙ`, possibly with named implicit arguments before `a₁`, is elaborated in a
different order: the leading implicit arguments of `f` are inserted as unknowns, its result type after the
`n` explicit arguments is unified with the expected type, and then the arguments are checked, in order.
This happens only if that result type does not depend on the explicit arguments and is an inductive family
applied, and only if the unification succeeds; otherwise it is undone, and the arguments are checked
first, as for any application. The unification adds no solution that the comparison of the application's
type with the expected type would not add afterwards. It gives the arguments types that only the expected
type determines. In the following program, `refl` is checked against `eq (3 + 1) 4`: the expected type
determines `P`, which no argument of `pack` does.

```hugin,run
%use "std/eq" (eq, refl).
witness : (A : Type) -> (A -> Type) -> Type.
pack : {A : Type} -> {P : A -> Type} -> (x : A) -> P x -> witness A P.
three : witness nat ([n] eq (n + 1) 4) = pack 3 refl.
%opaque three.
found : int -> rel.
found 3.
```

```output
found 3.
```

> **Rationale.** Lean 4 propagates the expected type into an application whose result does not depend on
> its explicit arguments, and Agda checks a constructor application by taking the parameters of its
> family from the target type first. The derivations of [`std/semantics`](../std/semantics.md) need it:
> the program and the rule of a step are known only from the type of the derivation.

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

## Implicit arguments by name

```text
NamedArg  ::= "{" (VAR | NAME) ":=" Expr "}"
App       ::= Expr (Expr | NamedArg)
```

An implicit argument can be given by the name of its binder: `f {x := e}` applies `f` to `e` as its
implicit argument `x`. `:=` is the two characters `:` and `=` without a space between them. The binder
must be one of the implicit binders of `f`'s type before its next explicit binder, and the implicit
arguments before it are inserted as unknowns, as for an application without names. `e` is checked against
the binder's type. The implicit arguments after `x` are not inserted yet: a further `{y := e'}` may give
one of them, and the next explicit argument or the expected type inserts the others. The names are those
of the declaration's binders, also of the binders that the free uppercase variables of a declaration give
([above](#implicit-arguments)): `vcons : A -> vec A N -> vec A (N + 1).` has the implicit binders `A` and
`N`.

It is an error ([E0926](../errors/E0926.md)) if no implicit binder before the next explicit one has the
name, or if `{x := e}` is not an argument of an application or a [pattern](clauses.md#implicit-patterns).

An implicit argument is given by name where nothing else determines it, as the middle point `y` of
`trans` from [`std/eq`](../std/eq.md) below, and where its explicit arguments determine it only up to an
application of a function that does not reduce:

```hugin,run
%use "std/eq".
%use "std/nat".
vec : Type -> nat -> Type.
vnil : vec A 0.
vcons : A -> vec A N -> vec A (N + 1).
zeroPlus : (n : nat) -> 0 + n ≡ n.
zeroPlus 0 = refl.
zeroPlus (N + 1) = cong suc (zeroPlus N).
cast : {n : nat} -> vec int (0 + n) -> vec int n.
cast {n := N} V = subst (vec int) (zeroPlus N) V.
addAll : vec int N -> int.
addAll vnil = 0.
addAll (vcons X Xs) = X + addAll Xs.
total : int -> rel.
total (addAll (cast {n := 2} (vcons 40 (vcons 2 vnil)))).
```

```output
total 42.
```

Without `{n := 2}`, the type of the argument, `vec int 2`, would have to match `vec int (plus 0 ?n)`,
which does not determine the unknown `?n` ([E0901](../errors/E0901.md)).

> **Rationale.** The spelling is that of Lean 4 (`f (x := e)`) and Rocq (`f (x:=e)`), with Agda's braces
> (`f {x = e}`): `{x = e}` is already a [record value](records.md#syntax) passed as an explicit argument.

## Definitions

```text
Definition ::= NAME Param* (":" Type)? "=" Expr "."
```

A *definition* gives a constant a value. Its forms are:

- `x : A = e.`: `e` is checked against the type `A`;
- `x = e.`: the type of `x` is the inferred type of `e`;
- `f p₁ … pₙ = e.` and `f p₁ … pₙ : A = e.`: `f` is the function `[p₁] … [pₙ] e`; a parameter `(x : T)`
  has the type `T`, and a parameter `X` an inferred type (in a type definition `t X : type = τ.`, `X`
  ranges over object types);
- `x : A = %postulate.` and `f p₁ … pₙ : A = %postulate.`: a [postulate](#postulates), a constant of type
  `A` (under the parameters) without a value.

A definition is a value: it is evaluated where it is used. Diagnostics, the language server and
`--print-after elaborate` show it by its name where a type or an implicit argument comes from it
(`w : vec2 = ident {vec2} v.` after `vec2 : Type = vec int two.` and `v : vec2`); conversion uses its
value. The binders of a declared type do not scope
over the definition. It is an error ([E0916](../errors/E0916.md)) to use them there:
`double : (x : int) -> int = x * 2.` is written `double (x : int) : int = x * 2.`, and `hugin fix` makes
this change.

A definition may compute with functions defined by clauses anywhere in the file, in its type and in its
value: it is elaborated after the clauses it needs ([Order of elaboration](index.md#order-of-elaboration)).
`two : nat = plus one one.` makes `eqn two (suc one)` and `eqn (suc one) (suc one)` the same type, also
when `plus` is defined after `two`. A definition that a function's clauses refer to while it applies the
function is in one cycle with the function: inside the cycle the type of a typed definition is known and
its value is not, and the function's applications do not reduce.

After a declaration `f : A.`, an item `f X₁ … Xₙ = e.` is a [clause](clauses.md) of `f`, not a
definition.

## Postulates

```text
Postulate ::= NAME Param* ":" Type "=" "%postulate" "."
```

A *postulate* `x : A = %postulate.` declares a constant of the meta type `A` without a value: an axiom.
Meta code that applies it is stuck, and it is an error ([E0909](../errors/E0909.md)) if object code
depends on a stuck value. A postulate can assume any statement, also a false one, so it is never
implicit: a declaration without a value or clauses that is not an inductive family or a constructor
declares a function without clauses, an error ([E0911](../errors/E0911.md)) unless one of its explicit
arguments has an empty type ([Clauses](clauses.md#syntax)). `%postulate` is only the definition of a declaration at the top level of
a file: elsewhere it is an error ([E0103](../errors/E0103.md)), and in a
[module body](../modules.md#module-bodies) [E0907](../errors/E0907.md). The parameters of a functor and
the fields of a signature are not postulates: they are bound to values where the functor is applied
or the signature ascribed ([Modules](../modules.md)).

The following program assumes that `0` is a right unit of `plus`, and uses the assumption in a proof.

```hugin,run
plus : nat -> nat -> nat.
plus 0 N = N.
plus (M + 1) N = plus M N + 1.
eqn : nat -> nat -> Type.
same : eqn N N.
plusZero : (n : nat) -> eqn (plus n 0) n = %postulate.
step : (n : nat) -> eqn (plus n 0) n -> nat.
step N _ = N.
toInt : nat -> int.
toInt 0 = 0.
toInt (N + 1) = toInt N + 1.
two : nat = step 2 (plusZero 2).
checked : int -> rel.
checked (toInt two).
```

```output
checked 2.
```

The option `--safe` of `hugin check` and `hugin run` rejects every postulate of the program and of the
files it imports ([E0925](../errors/E0925.md)); the standard library has none. The directive
`%assumptions f.` and the option `--print-assumptions f` print the postulates and trusted primitives
that `f` depends on ([Consistency](consistency.md#assumptions)).

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
2. the integer, if `A` is the meta `int` ([`std/int`](../std/int.md#the-meta-int)): unbounded, so also a
   literal beyond 64 bits;
3. a literal of `A` at the stage of its position, if `A` is another base type, or `int` at the object
   level, whose literals are 64-bit ([E0003](../errors/E0003.md));
4. if `A` is still an unknown, an unknown of type `A` that waits until the end of its item, or of the
   member of a module body that contains it. The literal is then checked against `A` as the item has
   determined it, by rule 1, 2 or 3; if `A` is still unknown, it is the meta `int`. The waiting literals
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

An operator that `%infix op f.` binds to meta functions applies the binding whose types fit, such as
`plus` for `+` on `nat` ([Operators bound to meta
functions](../lexical-structure.md#operators-bound-to-meta-functions)); the meanings below apply where
no binding fits. The arithmetic operators `+`, `-`, `*`, `/` and the negation `-x` apply to meta
integers as the functions `iplus`, `iminus`, `itimes`, `idiv` and `ineg` of
[`std/int`](../std/int.md#arithmetic), which are defined by clauses and computed natively on integers:
unbounded, with division rounded toward zero and `x / 0` equal to `0`. On meta floats and strings, `+`, `-`, `*`, `/` and `^` are computed at compile time as they
are on object values ([Arithmetic and comparisons](../object/arithmetic.md)); a result that is undefined
(a division by zero) is stuck. A literal operand takes the type and stage of the other operand.
Comparisons written with operators are always object formulas; meta integers are compared with the
functions `iequal`, `iless` and `ileq` of the prelude ([`std/int`](../std/int.md)), and atoms with
[`same`](../std/reflect.md#primitives).

A meta value of a base type used as object code is *persisted* as a literal
([Staging](staging.md#lifting)). It is an error ([E0909](../errors/E0909.md)) if its computation is
undefined or stuck, and ([E0930](../errors/E0930.md)) if it is a meta integer outside the object level's
64-bit range.

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
