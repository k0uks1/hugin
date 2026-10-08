# Universes

A *universe* is a type whose elements are types. Hugin has one universe of object types, `type`, and a
hierarchy of universes of meta types, `Type₀`, `Type₁`, …, written `Type`. This chapter defines them, their
levels and the types `rel` and `prop`.

## Syntax

```text
Universe ::= "type" | "Type"
```

## The universe of object types

`type` is the universe of object types: `int`, `string`, an open type `expr`, `list int` and every other
[object type](../object/types.md) are elements of `type`. A term whose type is an element of `type` has
stage 0: it is object code. The object level is first order, so `type` contains no function types; a
relation or constructor cannot take a type or a function as an argument
([E0908](../errors/E0908.md)). A binder over object types, as in a family `list A : type.`, is a meta
binder.

## The universes of meta types

`Type` is the universe of meta types. Each occurrence of `Type` stands for `Typeᵢ` for some *level*
*i* ≥ 0, which the compiler infers; levels are never written, and `--print-after elaborate` shows them
as `Type₁`, `Type₂`, … (and `Type₀` as `Type`). A term whose type is an element of a `Typeᵢ` has stage 1:
it is meta code.

The universes form a hierarchy:

- `Typeᵢ : Typeᵢ₊₁`;
- a function type `(x : A) -> B` and a record type `{ l₁ : A₁, … }` are in `Typeᵢ` if their components
  are;
- the universes are *cumulative*: a type in `Typeᵢ` is also in `Typeⱼ` for every *j* ≥ *i*;
- the lift `⇑A` of every object type `A`, also of `A = type`, is in `Type₀`.

It is an error ([E0904](../errors/E0904.md)) if the levels cannot be chosen consistently, in particular
if a universe is used as an element of itself. `Type : Type` is excluded because it would make the meta
level inconsistent and its evaluation possibly non-terminating.

Levels are global to a program: a definition has one level wherever it is used. There is no universe
polymorphism.

In the following program the signature `graph` has object types and relations as components, so it is
in `Type₀`; `holder` has a component of type `Type`, so it is in `Type₁`. `h.t` is the meta type `int` of
compile-time integers.

```hugin,run
graph : Type = { node : type, edge : node -> node -> rel }.
holder : Type = { t : Type }.
h : holder = { t = int }.
city : type.  berlin : city.
road : city -> city -> rel.
roads : graph = { node = city, edge = road }.
n : h.t = 42.
answer : int -> rel.
answer n.
```

```output
answer 42.
```

The following declaration is rejected: `mk` takes an element of `Type`, so `small` is in `Type₁`, and
`mk small` would put `small` into the universe it is defined in.

```hugin,compile_fail,E0904
small : Type.
mk : Type -> small.
loop : small = mk small.
```

## Relations and formulas

`rel` is the result type of relation types: `edge : node -> node -> rel` declares a relation. As a meta
type, `node -> node -> rel` is the type of object code that is a relation over `node`.

`prop` is the type of object formulas. A meta function whose result is `prop` is a
[formula function](staging.md#formula-functions): `cheap : item -> prop` takes object code of type
`item` and returns a formula.
