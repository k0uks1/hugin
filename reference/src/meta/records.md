# Records

A *record* is a meta value with named *fields*. Record types are the dependent sums of the meta level:
the type of a field may mention the fields before it. Record types are also the
[signatures](../modules.md#signatures) of modules, and modules are records. This chapter defines record
types, record values, projection and the subtyping of records.

## Syntax

```text
RecordType  ::= "{" FieldDecl ("," FieldDecl)* "}"
FieldDecl   ::= NAME ":" Type | "%complete" NAME
RecordValue ::= "{" NAME "=" Expr ("," NAME "=" Expr)* "}"
Projection  ::= Expr "." NAME
Update      ::= "(" Expr "with" "{" NAME "=" Expr ("," NAME "=" Expr)* "}" ")"
```

Braces also enclose module bodies, implicit binders and named patterns. The parser tells them apart by
their first tokens: `{` followed by a name and `:` starts a record type, a name and `=` a record value,
uppercase variables and `:` an implicit binder. A period at nesting depth 0 before the first `,` or `}`
makes the braces a module body ([Modules](../modules.md)). The requirement `%complete l` is described
with [signatures](../modules.md#signatures).

## Record types

`{ l₁ : A₁, …, lₙ : Aₙ }` is the type of records with the fields `l₁ … lₙ`. The type `Aᵢ` may refer to
the fields `l₁ … lᵢ₋₁`: in `{ node : type, edge : node -> node -> rel }` the type of `edge` mentions
`node`. A record type is in the universe of its field types ([Universes](universes.md)).

## Record values and projection

`{ l₁ = e₁, …, lₙ = eₙ }` is a record with the given fields. Its fields may be written in any order. It
is an error ([E0307](../errors/E0307.md)) to give a field twice.

`e.l` is the field `l` of the record `e`. It is an error ([E0906](../errors/E0906.md)) if `e` has no
field `l`. A projection from a record value is evaluated at compile time.

## Update

`(r with { l₁ = e₁, …, lₖ = eₖ })` at a meta position, where `r` is a record of type
`{ l₁ : A₁, … }`, is the record value with the fields `lᵢ` given by `eᵢ` and every other field `l`
projected from `r` as `r.l`. It is checked as that record value against the type of `r`: each `eᵢ`
against its field type, with the fields before it as updated, and a field kept from `r` must still have
its type after the fields before it changed. The update has the type of `r`. Since modules are records,
an update also adjusts a module or a functor argument: `tc (g with { edge = rail })`.

It is an error ([E0906](../errors/E0906.md)) if `r` is not a record or has no field `lᵢ`,
([E0307](../errors/E0307.md)) to give a field twice, and ([E0901](../errors/E0901.md)) if a value or a
kept field does not have its field type. At an object position, or if `r` is object code, the update is
the update of a fact ([Rules](../object/rules.md#records)).

The following program moves a point by an update, in a definition and in a function.

```hugin,run
point : Type = { x : int, y : int }.
origin : point = { x = 0, y = 0 }.
moved : point = (origin with { x = 5 }).
raise : point -> point = [p] (p with { y = p.y + 10 }).
at : int -> int -> rel.
at moved.x moved.y.
at (raise moved).x (raise moved).y.
```

```output
at 5 0.
at 5 10.
```

The following program applies the functor `tc` of [`std/graph`](../std/graph.md) to a graph and to
the same graph with another edge relation.

```hugin,run
%use "std/graph".
city : type.  a, b, c : city.
road : city -> city -> rel.
road a b.  road b c.
rail : city -> city -> rel.
rail c a.
g : graph = { node = city, edge = road }.
byRoad = tc g.
byRail = tc (g with { edge = rail }).
?- byRoad.path a X.
?- byRail.path c X.
```

```output
?- byRoad.path a X.
X = b.
X = c.
?- byRail.path c X.
X = a.
```

## Subtyping by coercion

A record of type `R` can be used where a record of type `R'` is expected if `R` has every field of `R'`
and the type of each such field can be used where the field's type in `R'` is expected. The compiler
inserts a coercion that builds a record with the fields of `R'`. Fields that `R'` does not mention are
dropped. It is an error ([E0204](../errors/E0204.md)) if a field of `R'` is missing.

The following program gives a record with three fields to a definition of type `point`, which has two.

```hugin,run
point : Type = { x : int, y : int }.
labelled = { x = 5, y = 6, name = "a" }.
corner : point = labelled.
coordinate : int -> rel.
coordinate corner.x.
coordinate corner.y.
named : string -> rel.
named labelled.name.
```

```output
coordinate 5.
coordinate 6.
named "a".
```

The following program has a dependent field: the type of `v` is the value of the field `t`.

```hugin,run
boxed : Type = { t : Type, v : t }.
parcel : boxed = { t = string, v = "inside" }.
content : string -> rel.
content parcel.v.
```

```output
content "inside".
```
