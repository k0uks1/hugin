# The meta level

The *meta level* is the compile-time language of Hugin. It is a total, dependently typed functional
language: a two-level type theory ([Annenkov et al. 2023](../notation.md#references)) whose outer level
is evaluated by the compiler and whose inner level is the [object level](../object/index.md) (Kovács
2022). Meta code computes object code: types, relations, rules and formulas. It never runs when the
object program is evaluated.

Every meta function terminates, and every meta function defined by clauses covers all its arguments.
Therefore the elaboration of every program terminates, and every application of a meta function to
closed arguments has a value.

## Stages

Every term has a *stage*: 0 for object code and 1 for meta code. The stage of a term is the stage of the
universe of its type ([Universes](universes.md)). The compiler infers where meta code must be turned
into object code and back ([Staging](staging.md)). A program does not write these quotes, and it writes
a splice only where it chooses to.

The following program defines a meta function by clauses over the prelude's natural numbers, and uses
its value in an object fact. The fact is computed at compile time.

```hugin,run
double : nat -> nat.
double zero = zero.
double (suc N) = suc (suc (double N)).
toInt : nat -> int.
toInt zero = 0.
toInt (suc N) = toInt N + 1.
result : int -> rel.
result (toInt (double 3)).
```

```output
result 6.
```

## Meta items

The meta level has the following items. Each is defined in the chapter given.

| item | meaning | defined in |
|---|---|---|
| `T : Δ -> Type.` | an inductive family | [Inductive families](families.md) |
| `c : Δ -> T ū.` | a meta constructor of the family `T` | [Inductive families](families.md) |
| `f : A.` followed by clauses `f p̄ = e.` | a meta function defined by clauses | [Clauses](clauses.md) |
| `x : A = e.` | a definition with a declared type | [Functions](functions.md#definitions) |
| `x = e.`, `f params = e.` | a definition with an inferred type | [Functions](functions.md#definitions) |
| `f params : A = e.` | a definition with parameters and a declared result type | [Functions](functions.md#definitions) |
| `f : … -> prop.` followed by rules `f t̄ :- φ.` | a formula function | [Staging](staging.md#formula-functions) |
| `x : A.` of any other meta type | a *postulate*: a constant without a value | below |

The items of a [module body](../modules.md#module-bodies) are those of a file, except the ones that a
body does not support ([E0907](../errors/E0907.md)); in particular, a body may declare meta functions
defined by clauses.

A declaration is classified by its type ([Declarations](../object/declarations.md#classification)): an
object type, relation or constructor type gives an object constant; any other type is checked as a meta
type. So `f : int -> int.` declares a meta function on compile-time integers, not a constructor.

A *postulate* has a type but no value. Meta code that applies it is stuck; it is an error
([E0909](../errors/E0909.md)) if object code depends on a stuck value.

## Order of elaboration

The items of a file may be written in any order: a name may be used before its declaration, and
functions may refer to each other without a keyword. The compiler elaborates the declarations,
definitions and clauses of a file in *dependency order*, and then its object items: rules, queries and
directives.

An item *depends on* the items whose names it mentions. A function defined by clauses has two parts, its
declaration (the *signature*) and its clauses (the *body*); so do a definition with a declared type
(`x : A = e.`: its type and its value) and a formula function (its declaration and its rules). A mention
of a function, a definition or a formula function depends on its body, since a type that computes with
it needs its value, and a body depends on its signature. A set of items that depend on each other,
directly or through other items, is a *cycle*; an item that is in no such set is a cycle of its own. The
compiler elaborates every cycle after the cycles that it depends on, and two cycles that do not depend on
each other in the order of their first items in the file.

So a type may compute with a function that is defined anywhere in the file. Here `plus`, its signature
and then its clauses, is elaborated before `vec3`, and `vec3` before `v`:

```hugin
nat : Type.
zero : nat.
suc : nat -> nat.
one : nat = suc zero.
vec3 : Type = vec int (plus one (suc one)).
v : vec3 = vcons 1 (vcons 2 (vcons 3 vnil)).
plus : nat -> nat -> nat.
plus zero N = N.
plus (suc M) N = suc (plus M N).
vec : Type -> nat -> Type.
vnil : vec A zero.
vcons : A -> vec A N -> vec A (suc N).
```

Inside a cycle, the signatures are elaborated first, then the bodies. No body of a cycle unfolds inside
the cycle, whatever the order in which the items are written: an application of one of its functions
does not reduce, and one of its definitions is not replaced by its value, until the whole cycle is
elaborated. A type in the cycle that needs such a value does not match ([E0901](../errors/E0901.md)), and
the error names the cycle in a note. In the following file, the type of `d` needs `k zero`, and
the clauses of `k` need `d`; `d` is rejected, also when the clauses of `k` are written before it:

```hugin,compile_fail,E0901
nat : Type.
zero : nat.
suc : nat -> nat.
vec : Type -> nat -> Type.
vnil : vec A zero.
vcons : A -> vec A N -> vec A (suc N).
vlen : vec A N -> nat.
vlen vnil = zero.
vlen (vcons X Xs) = suc (vlen Xs).
d : vec int (k zero) = vcons 1 vnil.
k : nat -> nat.
k zero = suc zero.
k (suc N) = vlen d.
```

When the bodies of a cycle are elaborated, the termination of its functions
([Termination](termination.md)) and the cycles of its formula functions ([E0105](../errors/E0105.md))
are checked; only then do its bodies unfold, in the later cycles. A value that the cycle computed with an
application that did not reduce is computed further where it is used.

It is an error ([E0105](../errors/E0105.md)) if a definition refers to itself, and
([E0101](../errors/E0101.md)) if definitions refer to each other in a cycle; recursion is written with
clauses. An item with an error is reported and left out; elaboration continues with the next item. A use
of a name that such an item declared, or that a `%use` that was left out might have opened
([Modules](../modules.md)), is not reported again: its item is left out without a further diagnostic.
The same holds for a function whose clauses have an error, which is left undefined, and for the
definitions and functions that use it: a use of one of them, which would need the function's value, is
left out without a further diagnostic too. A module body is part of the item that contains it, and its
items are elaborated inside that item ([Modules](../modules.md#module-bodies)).

The unknowns that the compiler creates while it elaborates an item (implicit arguments, inferred types,
holes) belong to that item. The clauses of one function, and of one formula function, count as one item.
An item solves its own unknowns; the unknowns of earlier items are fixed while it is elaborated, so a
later item never changes what an earlier one means. Unknowns are numbered from `?0` within each item in
diagnostics. In a module body, the clauses of each member function count as one item inside the item
that contains the body: the unknowns of the body's declarations and definitions are fixed while the
clauses are elaborated, and the declaration of a member function must solve its own unknowns
([E0903](../errors/E0903.md)), as a declaration of a file does.

The option `--print-after elaborate` prints the elaborated program: meta definitions with the inserted
quotes `⟨…⟩`, splices `$…` and implicit arguments, the compiled clauses of functions, and the object
items after staging. Types and implicit arguments are printed with definitions by their names, as in
diagnostics ([Definitions](functions.md#definitions)).

## Meta types

The meta types are

- the universes `Type`, `Type₁`, … and `type` ([Universes](universes.md));
- function types `(x : A) -> B`, `A -> B` and `{x : A} -> B` ([Functions](functions.md));
- record types `{ l₁ : A₁, …, lₙ : Aₙ }` ([Records](records.md));
- inductive families ([Inductive families](families.md));
- the base types `int`, `float` and `string` used as meta types: compile-time numbers and strings
  ([Functions](functions.md#literals-and-primitive-operations));
- the *lifted* object types `⇑A`, whose values are object code of type `A`, and the types of object
  relations and formulas ([Staging](staging.md));
- `sym` and the reflective types of `std/reflect` ([Reflection](../reflection.md)).

## Unused definitions

A meta definition or formula function of the program that nothing refers to is reported
([W0003](../errors/W0003.md), lint `unused_definitions`). Module values, signatures and type definitions
are exempt.
