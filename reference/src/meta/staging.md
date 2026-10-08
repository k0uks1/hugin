# Staging

*Staging* turns a Hugin program into an object program: the compiler evaluates the meta code that object
items use and keeps the object code that results. This chapter defines object code as a meta value, the
lift `⇑`, the inferred quotes and splices, the explicit splice `$`, the persistence of compile-time values,
formula functions, and the instances that staging creates.

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

- a *quote* `⟨t⟩` turns object code `t` into a meta value of type `⇑A`;
- a *splice* `$e` turns a meta value `e : ⇑A` into object code of type `A`;
- `⇑` is inserted where an object type is used as a meta type.

Functions are converted by eta-expansion: a relation of type `⇑(A -> rel)` can be passed where a formula
function `⇑A -> ⇑prop` is expected. `--print-after elaborate` shows the inserted quotes and splices.

It is an error ([E0902](../errors/E0902.md)) if a meta value is used as object code and is not object
code or a value of a base type, or if object code is used where a compile-time value is needed.

```hugin,compile_fail,E0902
nat : Type.
zero : nat.
q : int -> rel.
q zero.
```

The explicit splice `$e` states a conversion that stage inference would insert. It is needed where the
stage of a term is not determined by its context, and it is the notation of
[holes](../reflection.md#holes) in quoted syntax. The explicit lift `⇑A` writes the type of object code.

## Persistence

A meta value of a base type (`int`, `float`, `string`) used as object code is *persisted*: it becomes
the literal of its value. Arithmetic in object code whose operands are both meta values is computed at
compile time and persisted. It is an error ([E0909](../errors/E0909.md)) if such a value is undefined (an
overflow, a division by zero) or does not evaluate to a literal, for example because it applies a
postulate.

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
