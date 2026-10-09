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

The following program defines a meta function by clauses over a meta type of natural numbers, and uses
its value in an object fact. The fact is computed at compile time.

```hugin,run
nat : Type.
zero : nat.
suc : nat -> nat.
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

A declaration is classified by its type ([Declarations](../object/declarations.md#classification)): an
object type, relation or constructor type gives an object constant; any other type is checked as a meta
type. So `f : int -> int.` declares a meta function on compile-time integers, not a constructor.

A *postulate* has a type but no value. Meta code that applies it is stuck; it is an error
([E0909](../errors/E0909.md)) if object code depends on a stuck value.

## Order of elaboration

The items of a file may be written in any order. The compiler elaborates the declarations and definitions
first, each after the items it refers to, then the clauses of functions, which may refer to every
declaration and to each other, and then the object items: rules, queries and directives. It is an error
([E0105](../errors/E0105.md)) if a definition refers to itself, and ([E0101](../errors/E0101.md)) if
definitions refer to each other in a cycle; recursion is written with clauses. An item with an error is
reported and left out; elaboration continues with the next item.

The option `--print-after elaborate` prints the elaborated program: meta definitions with the inserted
quotes `⟨…⟩`, splices `$…` and implicit arguments, the compiled clauses of functions, and the object
items after staging.

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
- `sym` and the reflective types of the prelude ([Reflection](../reflection.md)).

## Unused definitions

A meta definition or formula function of the program that nothing refers to is reported
([W0003](../errors/W0003.md), lint `unused_definitions`). Module values, signatures and type definitions
are exempt.
