# Staging

*Staging* turns a Hugin program into an object program: the compiler evaluates the meta code that object
items use and keeps the object code that results. This chapter defines object code as a meta value, the
lift `⇑`, the inferred quotes and splices, the explicit splice `$`, the lifting of compile-time values into
object code, formula functions, and the instances that staging creates.

## Syntax

```text
Lift    ::= "⇑" Expr
Splice  ::= "$" Expr
```

## Object code

For an object type `A`, the meta type `⇑A` (*lift* of `A`) is the type of *object code* of type `A`: a
term of the object level that is not evaluated at compile time. Its values can be passed around, stored
in records and returned by functions, and they are inserted into object items, but they cannot be
inspected: a meta function cannot match on a value of type `⇑A`. (To inspect object syntax, programs use
the [reflective types](../reflection.md).)

The types of relations (`node -> node -> rel`) and of formulas (`prop`) are object types in this sense:
a meta value of type `node -> node -> rel` is object code that denotes a relation, and one of type `prop`
is a formula.

## Stage inference

Every term is elaborated at the stage of its expected type ([The meta level](index.md#stages)). When the
expected type is object code and the term is a meta value, or the reverse, the compiler inserts the
conversion (Kovács 2022):

- a *quote* `⟨t⟩` turns object code `t` into a meta value of type `⇑A` (it is inserted, never written;
  the quotes `'{ … }` of [reflection](../reflection.md#quotes) are another construct: they make data of
  the reflective types, not object code);
- a *splice* `$e` turns a meta value `e : ⇑A` into object code of type `A`;
- a meta value of a base type or of a [shared data type](families.md#shared-data) used as object code is
  converted by its [lifting](#lifting);
- `⇑` is inserted where an object type is used as a meta type.

Functions are converted by eta-expansion: a relation of type `⇑(A -> rel)` can be passed where a formula
function `⇑A -> ⇑prop` is expected. `--print-after elaborate` shows the inserted quotes and splices.

It is an error ([E0902](../errors/E0902.md)) if a meta value is used as object code and its type has no
lifting, or if object code is used where a compile-time value is needed.

```hugin,compile_fail,E0902
nat : Type.
zero : nat.
q : int -> rel.
q zero.
```

The explicit splice `$e` states a conversion that stage inference would insert: `e` is meta code, and a
value of a type with a lifting is lifted. It is needed where the
stage of a term is not determined by its context. Inside a reflection quote `'{ … }`, `$` marks a
[hole](../reflection.md#holes) instead; outside a quote it is always the splice. The explicit lift `⇑A` writes the type of object code.

## Lifting

A meta value is used as object code by its *lifting*: a meta function `ℓ : τ -> ⇑τ⁰` that turns values of
the meta type `τ` into object code of the object type `τ⁰`. The lifting of a type, if it exists, is given
by the following rules, of which at most one applies to each type:

```text
                              (a ↦ f) ∈ Δ
  ─────────────────── Base   ──────────── Param   ─────────────── Code
  Δ ⊢ b ⇝ persist_b          Δ ⊢ a ⇝ f            Δ ⊢ ⇑A ⇝ [x] x
  (b ∈ int, float, string)

  T shared    Δ ⊢ τ₁ ⇝ ℓ₁   …   Δ ⊢ τₙ ⇝ ℓₙ
  ──────────────────────────────────────────── Shared
  Δ ⊢ T τ₁ … τₙ ⇝ T.lift ℓ₁ … ℓₙ
```

with `b⁰ = b`, `(⇑A)⁰ = A` and `(T τ̄)⁰ = T τ̄⁰`. `Δ` maps the parameters of a [shared data
type](families.md#shared-data) to the liftings of its elements; stage inference uses the rules with `Δ`
empty. The rule *Lift* of stage inference states that a meta value `e : τ` used where object code of
type `A` is expected, with `τ⁰` a subtype of `A`, is the object code `$(ℓ e)`, for the lifting `ℓ` of `τ`.

A value of a base type is *persisted*: it becomes the literal of its value. A value of object code is
spliced. A value of a shared data type becomes the object term of the same constructors, whose
arguments are lifted in turn: a compile-time `[2, 3] : list int` used as object code is the term
`cons 2 (cons 3 nil)`, which a rule head derives as a fact with its subfacts. A compile-time list of object
code, `list (⇑int)`, is the object list of that code. It is an error ([E0902](../errors/E0902.md)) if the
type has no lifting; the error names the first type that is not shared.

Arithmetic in object code whose operands are both meta values is computed at compile time and
persisted. It is an error ([E0909](../errors/E0909.md)) if such a value is undefined (an overflow, a
division by zero) or does not evaluate to a literal, for example because it applies a postulate.

The following program persists a compile-time integer, explicitly with `$` and implicitly, and passes
object code of type `⇑int`.

```hugin,run
limit : int = 2 + 3.
code : ⇑int = 4.
n : int -> rel.
n $limit.
n (limit + 1).
n code.
```

```output
n 4.
n 5.
n 6.
```

The following program states a list and an optional value computed at compile time as facts.

```hugin,run
primes : list int = [2, 3, 5, 7].
first : option int = some 2.
listed : list int -> rel.
listed primes.
chosen : option int -> rel.
chosen first.
?- listed L, len L N.
?- chosen X.
```

```output
?- listed L, len L N.
L = cons 2 (cons 3 (cons 5 (cons 7 nil))), N = 4.
?- chosen X.
X = some 2.
```

> **Rationale.** Lifting serialises a compile-time value: the object level has literals and the
> identities of facts, so a meta value can only be represented by a term that denotes it, never by
> reference. Base types are the base case; shared data types are the types whose values are such terms
> (Kovács 2022 calls the map from a meta inductive type into object code a lifting, and shows that it
> exists in one direction only).

## Formula functions

A *formula function* is a meta function whose result type is `prop`. Its arguments of object types are
object code, so `cheap : item -> prop` has the meta type `⇑item -> ⇑prop`. An atom whose name is a formula
function is replaced by the formula that the function returns. A formula function is defined

- by a definition, `cheap : item -> prop = [I] I.price < 10.`, or
- by rules: after a declaration `f : τ₁ -> … -> τₙ -> prop.` without a definition, every rule
  `f t₁ … tₙ :- φ.` of the file is a clause of `f`. The function stands for the disjunction of its clauses:
  `f x̄` is `(x̄ = t̄₁, φ₁) ; … ; (x̄ = t̄ₖ, φₖ)`.

The variables of a clause other than its arguments are local to each use: every application gets fresh
variables (*hygiene*). A formula function without clauses is always false; the compiler warns about it
([W0005](../errors/W0005.md), lint `empty_formula_functions`).

The following program defines grandparenthood as a formula function. Its variable `Y` does not capture
the variable `Y` of the rule that uses it.

```hugin,run
person : type. ann : person. bob : person. cy : person. dan : person.
parent : person -> person -> rel.
parent dan ann. parent ann bob. parent bob cy.
grand : person -> person -> prop.
grand X Z :- parent X Y, parent Y Z.
middle : person -> person -> rel.
middle X Y :- grand X _, parent Y X.
?- middle X Y.
```

```output
?- middle X Y.
X = ann, Y = dan.
```

## Instances

Staging creates object constants in two ways.

- A [family](../object/types.md#families) of object constants is a meta function from object types to
  object constants. Its applications are memoised by their normalised arguments: two uses of `len` at
  `list int` are one relation `len[int]`. The rules of a family are staged once per instance that the
  program uses.
- A [module body](../modules.md) is *generative*: evaluating it creates fresh object constants. Two
  applications of a functor to the same arguments in two definitions are two instances with distinct
  relations.

It is an error ([E0205](../errors/E0205.md)) if staging a family's rules needs infinitely many instances.
