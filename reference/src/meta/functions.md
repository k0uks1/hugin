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
implicit argument and solves it by higher-order pattern unification with the types around it. It is an
error ([E0903](../errors/E0903.md)) if an implicit argument or a type is not determined. Implicit
arguments cannot be written explicitly; they are inferred from the explicit arguments and the expected
type.

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

A definition is a value: it is evaluated where it is used. The binders of a declared type do not scope
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
rest of the item may constrain. Every hole is an error ([E0924](../errors/E0924.md)), whose diagnostic
reports the goal and the variables in scope. The items around a hole are still elaborated, so all holes
are reported at once; compilation stops before staging. The name of a hole only identifies it in
messages.

The following program leaves the argument of the outer `suc` as a hole. The compiler reports its goal,
`nat`.

```hugin,compile_fail,E0924
nat : Type.
zero : nat.
suc : nat -> nat.
double : nat -> nat.
double zero = zero.
double (suc N) = suc (suc ?).
```

> **Note.** Holes support writing a program step by step. The language server shows the goal of a hole,
> and offers to split cases and to add missing clauses, with holes for their right-hand sides.

## Literals and primitive operations

A literal checked against a meta type is a *meta value*: `3 : int` is a compile-time integer. A literal
checked against a type with a constant constructor and a constructor with one recursive argument, such as
`nat` with `zero` and `suc`, is the numeral `suc (… zero)` ([Inductive families](families.md#numerals)).
A literal whose type is not determined is a meta value of its base type.

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
