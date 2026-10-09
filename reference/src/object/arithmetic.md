# Arithmetic and comparisons

Terms of base types can be computed with arithmetic operators and compared. This chapter defines the
operators, their types and the cases in which they are undefined.

## Syntax

```text
Term      ::= Term ("+" | "-" | "^") Term
            | Term ("*" | "/") Term
            | "-" Term
            | VAR | "_" | INT | FLOAT | STRING
            | QualifiedName Term*                     (a constructor term or fact)
            | "(" Term ")"
            | Projection | Update | AsPattern | Ascription
Comparison ::= Term ("=" | "<>" | "<" | "<=" | ">" | ">=") Term
```

The precedence of the operators is given in [Lexical
structure](../lexical-structure.md#operators-and-precedence).

## Arithmetic

| operator | operands | result |
|---|---|---|
| `a + b`, `a - b`, `a * b` | two `int` or two `float` | sum, difference, product |
| `a / b` | two `int` | quotient, rounded toward zero |
| `a / b` | two `float` | quotient |
| `- a` | `int` or `float` | negation |
| `a ^ b` | two `string` | concatenation |

Both operands of a binary operator have the same base type; a refinement counts as its base type, and the
result has the base type. A literal operand takes the type of the other operand. It is an error
([E0402](../errors/E0402.md)) if the operand types differ or do not fit the operator.

An operation is *undefined* if its integer result does not fit into 64 bits, or if it divides by zero
(for `int` and for `float`). A formula that contains an undefined operation does not hold, so the rule
instance does not fire. The operations never produce a NaN.

An arithmetic term in an argument of a body atom is computed, not matched: its variables must be bound
before the atom ([range restriction](rules.md#range-restriction)).

The following program computes with integers, floats and strings. Integer division rounds toward zero.
The rule instance that divides by zero does not fire.

```hugin,run
sample : int -> rel.
sample 7. sample 0.
quotient : int -> int -> rel.
quotient X Q :- sample X, Q = -X / 2.
inverse : int -> int -> rel.
inverse X I :- sample X, I = 100 / X.
half : float -> rel.
half H :- H = 7.0 / 2.0.
greeting : string -> rel.
greeting G :- G = "hello, " ^ "world".
%output quotient. %output inverse. %output half. %output greeting.
```

```output
greeting "hello, world".
half 3.5.
inverse 7 14.
quotient 0 0.
quotient 7 (-3).
```

## Constant expressions

An arithmetic term whose operands are literals is computed when the program is compiled. If it is
undefined, its formula never holds, and the compiler warns ([W0001](../errors/W0001.md), lint
`undefined_constant_expressions`).

The following program has a constant expression that overflows. Its rule never fires, and the compiler
warns about it.

```hugin,run
overflow : int -> rel.
overflow X :- X = 9223372036854775807 + 1.
ok : int -> rel.
ok 1.
%output ok. %output overflow.
```

```output
ok 1.
```

## Comparisons

A comparison `t op u` holds if the values of `t` and `u` stand in the relation *op*.

- `=` and `<>` compare two terms of the same base type, or two terms of types of facts. Facts are
  compared structurally, by their constant and their arguments ([Facts and identity](facts.md)).
- `<`, `<=`, `>` and `>=` compare two terms of the same base type. Integers and floats are ordered by
  value, strings by their code points, lexicographically.

It is an error ([E0402](../errors/E0402.md)) to compare terms of different base types, or to order
terms that are not of a base type.

An equation `X = t` in which `X` is not bound when it is reached in the canonical order is a *binding
equation*: it binds `X` to the value of `t`. Every other comparison is a *test*, and its variables must
be bound.

The following program orders strings and compares facts.

```hugin,run
city : (name : string) -> rel.
city "berlin". city "athens". city "cairo".
before : string -> string -> rel.
before A B :- city A, city B, A < B.
not_berlin : city -> rel.
not_berlin C :- city N, C = city N, C <> city "berlin".
?- before "athens" B.
?- not_berlin C.
```

```output
?- before "athens" B.
B = "berlin".
B = "cairo".
?- not_berlin C.
C = city "athens".
C = city "cairo".
```
