# Staging

*Staging* turns a Hugin program into an object program: the compiler evaluates the meta code that object
items use and keeps the object code that results. This chapter defines object code as a meta value, the
lift `⇑`, the inferred quotes and splices, the explicit quote `<t>` and splice `$`, the lifting of meta
values into object code, formula functions, and the instances that staging creates.

## Syntax

```text
Lift    ::= ("⇑" | "^") Expr
Quote   ::= "<" Expr ">"
Splice  ::= "$" Expr
```

## Object code

For an object type `A`, the meta type `⇑A` (*lift* of `A`) is the type of *object code* of type `A`: a
term of the object level that is not evaluated at compile time. Its values can be passed around, stored
in records and returned by functions, and they are inserted into object items, but they cannot be
inspected: a meta function cannot match on a value of type `⇑A`. Programs that inspect object syntax use
the [reflective types](../reflection.md). Object code is
[object-typed](../object/types.md#where-object-code-is-typed) where it is written.

The types of relations (`node -> node -> rel`) and of formulas (`prop`) are object types in this sense:
a meta value of type `node -> node -> rel` is object code that denotes a relation, and one of type `prop`
is a formula.

## Stage inference

Every term is elaborated at the stage of its expected type ([The meta level](index.md#stages)). When the
expected type is object code and the term is a meta value, or the reverse, the compiler inserts the
conversion ([Kovács 2022](../notation.md#references)):

- a *quote* `⟨t⟩` turns object code `t` into a meta value of type `⇑A`. It is inserted, or written as
  `<t>` ([Explicit quotes](#explicit-quotes)). The quotes `'( … )` of
  [reflection](../reflection.md#quotes) are a different construct, which makes data of the reflective
  types;
- a *splice* `$e` turns a meta value `e : ⇑A` into object code of type `A`;
- a meta value of a base type or of a [shared data type](families.md#shared-data) used as object code is
  converted by its [lifting](#lifting);
- `⇑` is inserted where an object type is used as a meta type.

Functions are converted by eta-expansion: a relation of type `⇑(A -> rel)` can be passed where a formula
function `⇑A -> ⇑prop` is expected. `--print-after elaborate` shows the inserted quotes and splices.

`⇑` is *covariant*: a value of type `⇑A` is accepted where a value of type `⇑B` is expected if `A` is a
[subtype](../object/types.md#subtyping) of `B`. Nothing is inserted. The same holds where a value
`e : ⇑A` is used as object code in a position that is itself quoted, such as an argument of a meta
function that takes `⇑B`: the quote cancels the splice, and `e` is passed as it is. A function type is
contravariant in its domain, so a function on `⇑expr` is accepted where a function on `⇑var` is expected
if `var` is a subtype of `expr`. Record types are related field by field. Any other type that contains
`⇑`, such as `list (⇑A)`, is related to another only by equality. It is an error
([E0901](../errors/E0901.md)) otherwise, or ([E0204](../errors/E0204.md)) for a field of a record.
Spliced code in an object position is not a meta-level conversion; it is typed by object typing
([Object types](../object/types.md#typing-of-rules)).

It is an error ([E0902](../errors/E0902.md)) if a meta value is used as object code and its type has no
lifting, or if object code is used where a meta value is needed.

The following program is rejected: `zero` is a value of the meta type `nat`, which has no lifting, in a
column of type `int`.

```hugin,compile_fail,E0902
nat : Type.
zero : nat.
level : int -> rel.
level zero.
```

The following program passes object code of type `var` where object code of type `expr` is expected.

```hugin,run
expr : type.
var : type.
var <: expr.
v : int -> var.
term : (x : expr) -> rel.
mentioned : expr -> prop.
mentioned X = term X.
named : var -> prop.
named X = mentioned X.
term (v 1).
vars : (x : var) -> rel.
vars (v 1). vars (v 2).
found : (x : var) -> rel.
found X :- vars X, named X.
?- found X.
```

```output
?- found X.
X = v 1.
```

The following function is rejected: `X` is object code of type `expr`, and `narrow` takes object code of
type `var`, a subtype of `expr`.

```hugin,compile_fail,E0901
expr : type.
var : type.
var <: expr.
vars : (v : var) -> rel.
narrow : var -> prop.
narrow X = vars X.
widen : expr -> prop.
widen X = narrow X.
```

The explicit splice `$e` states a conversion that stage inference would insert: `e` is meta code, and a
value of a type with a lifting is lifted. It is needed where the context of a term does not determine
its stage. Inside a reflection quote `'( … )`, `$` marks a [hole](../reflection.md#holes) instead;
outside a quote it is always the splice. The explicit lift `⇑A` writes the type of object code; `^A` is
its ASCII spelling, and the compiler prints `⇑A`.

## Explicit quotes

An *explicit quote* `<t>` states the quote that stage inference would insert: `t` is object code, and
`<t>` is a meta value of type `⇑A`, where `A` is the object type of `t`. Checked against `⇑A`, `t` is
checked against `A` at the object stage, with the rules of stage inference inside it: a meta value of
type `⇑B` in `t` is spliced, by `$` or by inference. `<$e>` is `e`, and `$<t>` is `t`. The compiler prints
an inserted or written quote as `⟨t⟩`.

`<` opens a quote only where an operand starts; between two operands it is a comparison
([Operators and precedence](../lexical-structure.md#operators-and-precedence)). The content of a quote
is parsed above the comparisons, so that the next `>` closes it, and an argument that is a quote is
parenthesised: `f (<t>)`. It is an error ([E0005](../errors/E0005.md)) if a quote is not closed.

The following program writes the quotes of two definitions. Stage inference would give them the same
types without the quotes: `trip = road oslo rome.` is also a value of type `⇑rel`.

```hugin,run
city : type. oslo : city. rome : city.
road : city -> city -> rel.
road oslo rome.
trip = <road oslo rome>.
back : ^city -> ^city -> ^prop = [x] [y] <road $y $x>.
linked : rel.
linked :- $trip.
returns : rel.
returns :- $(back (<rome>) (<oslo>)).
%output linked. %output returns.
```

```output
linked.
returns.
```

> **Rationale.** The splice stays `$`, which is already explicit and is inferred where it is left out.
> Kovács's language dtt-rtcg (`AndrasKovacs/dtt-rtcg`) pairs `<t>` with a splice `~t`, and his staged
> elaborator ([Kovács 2022](../notation.md#references)) with `[t]`; a second splice
> notation would give one operation two spellings. Inside a reflection quote, `$` marks a hole: there
> too it inserts a meta value into quoted syntax, and the quote around it says which kind.

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
empty. The rule *Lift* of stage inference states that a meta value `e : τ` used where object code of type
`A` is expected, with `τ⁰` a subtype of `A`, is the object code `$(ℓ e)`, for the lifting `ℓ` of `τ`.

A value of a base type is *persisted*: it becomes the literal of its value. A value of object code is
spliced. A value of a shared data type becomes the object term of the same constructors, whose arguments
are lifted in turn: a compile-time `[2, 3] : list int` used as object code is the term
`cons 2 (cons 3 nil)`, which a rule head derives as a fact with its nested facts. A compile-time list of
object code, `list (⇑int)`, is the object list of that code. It is an error ([E0902](../errors/E0902.md))
if the type has no lifting; the error names the first type that is not shared.

Arithmetic in object code whose operands are both meta values is computed at compile time and
persisted. It is an error ([E0909](../errors/E0909.md)) if such a value is undefined (an overflow, a
division by zero) or does not evaluate to a literal, for example because it applies a postulate.

The following program persists a compile-time integer, explicitly with `$` and implicitly, and passes
object code of type `⇑int`.

```hugin,run
limit : int = 2 + 3.
code : ⇑int = 4.
size : int -> rel.
size $limit.
size (limit + 1).
size code.
```

```output
size 4.
size 5.
size 6.
```

The following program states a list and an optional value computed at compile time as facts.

```hugin,run
%use "std/list".
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

> **Rationale.** Lifting serialises a meta value: the object level has literals and the
> identities of facts, so a meta value can only be represented by a term that denotes it, never by
> reference. Base types are the base case; shared data types are the types whose values are such terms.
> The name follows Kovács 2022, where a lifting maps a meta inductive family into object code and exists
> in one direction only.

## Formula functions

A *formula function* is a meta function whose result type is `prop`. Its arguments of object types are
object code, so `cheap : item -> prop` has the meta type `⇑item -> ⇑prop`. An atom whose name is a
formula function is replaced by the formula that the function returns. A formula function is defined

- by a definition, `cheap : item -> prop = [I] I.price < 10.`, or
- by rules: after a declaration `f : τ₁ -> … -> τₙ -> prop.` without a definition, every rule
  `f t₁ … tₙ :- φ.` of the file is a clause of `f`. The function stands for the disjunction of its
  clauses: `f x̄` is `(x̄ = t̄₁, φ₁) ; … ; (x̄ = t̄ₖ, φₖ)`.

Each clause of a formula function is [typed](../object/types.md#where-object-code-is-typed) where it
is written, like a rule whose body is the clause's body and the equations of its arguments. The
variables of a clause other than its arguments are local to each use: every application gets fresh
variables (*hygiene*). A formula function without clauses is always false; the compiler warns about it
([W0005](../errors/W0005.md), lint `empty_formula_functions`).

A use of a formula function is replaced by its formula, so a formula function cannot refer to itself:
it is an error ([E0105](../errors/E0105.md)) if its clauses use it, directly or through other formula
functions, definitions or functions whose expansion uses it. Recursion is written with a relation. The
error is reported once for each such cycle; the formula functions of the cycle are then left out, and so
are their uses, without a further diagnostic.

```hugin,compile_fail,E0105
node : type.
edge : node -> node -> rel.
linked : node -> node -> prop.
linked X Z :- edge X Y, linked Y Z.
```

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
