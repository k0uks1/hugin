# Object types

An *object type* classifies the values of the object level. The object types are the elements of the
universe `type`. This chapter defines the object types, the subtype relation between them, families of
object constants and the typing of rules.

## Syntax

```text
ObjectType ::= NAME ObjectTypeArg*            (a base type, a declared type or a family instance)
             | ObjectType "|" ObjectType      (a union)
             | "(" ObjectType ")"
ObjectTypeArg ::= NAME | VAR | "(" ObjectType ")"
```

An object type is written as a name, the application of a family to object types (`list int`,
`pair string (option int)`), or a union of such types.

## Base types

The *base types* are `int` (64-bit signed integers), `float` (64-bit IEEE 754 numbers) and `string`
(sequences of Unicode code points). The names `int`, `float` and `string` are in scope in every program
that includes the prelude. A program compiled with `--no-prelude` declares the base types it uses with
`%builtin`:

```text
BuiltinType ::= NAME ":" "type" "=" "%builtin" ("int" | "float" | "string") "."
```

The following program is valid with and without the prelude, since it declares its base types itself.

```hugin,run
num : type = %builtin int.
text : type = %builtin string.
word : num -> text -> rel.
word 1 "one".
```

```output
word 1 "one".
```

## Open types

An *open type* is declared `a : type.`. Its *members* are

- the constructors whose result type is `a`, and
- the relations, structs and constructors `c` with a *subtyping edge* `c <: a.`

```text
SubtypeEdge ::= Expr "<:" Expr "."
```

A value of type `a` is the identity of a fact of one of the members. It is an error
([E0404](../errors/E0404.md)) if the left side of an edge is not a fact type or the right side is not an
open type.

The following program declares an open type `staff` whose members are the relation `teacher`, by an
edge, and the constructor `janitor`.

```hugin,run
staff : type.
teacher : (name : string) -> (subject : string) -> rel.
teacher <: staff.
janitor : (name : string) -> staff.
on_duty : staff -> rel.
on_duty (teacher "cy" "math").
on_duty (janitor "dee").
?- on_duty S.
```

```output
?- on_duty S.
S = janitor "dee".
S = teacher "cy" "math".
```

## Fact types

Every relation, struct and constructor `c` is also a type, the *fact type* `c`. Its values are the
identities of the facts of `c` ([Facts and identity](facts.md)). A fact type is a subtype of the open
type of its constructor and of every open type it has an edge to.

## Unions

A *union* `τ₁ | … | τₙ` is the type of the values of any of its members. The members of a union are
fact types or unions of fact types, and do not overlap; it is an error
([E0404](../errors/E0404.md)) otherwise. A type is *closed* if it is a fact type or a union of closed
types. Projections and updates apply only to closed types ([Records](rules.md#records)), since a closed
type has a known set of members.

A union is written in a type definition (`term : type = var | abs.`) or directly in a column type.

## Refinements

A *refinement* `a : type <: b.`, where `b` is a base type or a refinement, declares a type whose
values are values of `b`. It is nominal: a value of type `b` is not a value of type `a`, but a literal
of the base type of `b` may be used where an `a` is expected. It is an error
([E0404](../errors/E0404.md)) if `b` is not a base type or refinement, or if refinements form a cycle.

The following program declares ages as a refinement of `int`. The literal `30` is an age; arithmetic on
an age gives an `int`.

```hugin,run
age : type <: int.
person : (name : string) -> (years : age) -> rel.
person "ann" 30.
next_year : string -> int -> rel.
next_year N M :- person N A, M = A + 1.
%output next_year.
```

```output
next_year "ann" 31.
```

## Type definitions

A *type definition* `a : type = τ.` makes `a` stand for the object type `τ`. A type definition with
parameters, `a X₁ … Xₙ : type = τ.`, is a meta function from object types to an object type, and
`a τ₁ … τₙ` stands for `τ` with the parameters replaced. Type definitions are unfolded wherever they are
used. It is an error ([E0104](../errors/E0104.md)) if type definitions refer to each other in a cycle.

## Families

A declaration whose head has parameters, or whose type has free uppercase variables, declares a *family*
of object constants:

- `list A : type.` declares a family of open types;
- `nil : list A.` and `cons : A -> list A -> list A.` declare families of constructors; the free
  variable `A` is an implicit parameter that ranges over object types;
- `len : (l : list A) -> (n : int) -> rel.` declares a family of relations;
- `pair A B : type = { fst : A, snd : B }.` declares a family of structs.

The application of a family to object types is an *instance*. Two applications to the same types are the
same instance: `list int` in two places is one type, and `len` used at lists of integers is one
relation. Instances are named after their arguments, `list[int]` and `len[int]`, in diagnostics and in
the output of `--print-after`; facts and query answers show the name of the family.

The type arguments of a use of a family are inferred from the types of the terms around it. It is an
error ([E0206](../errors/E0206.md)) if nothing determines them; an ascription such as `(nil : list int)`
supplies them. It is an error ([E0205](../errors/E0205.md)) if a recursive rule of a family uses the
family at other type arguments than its own (polymorphic recursion), since that would need infinitely
many instances.

The following program uses the prelude's family `list` at two element types; the same rule of `len`
measures both.

```hugin,run
nums : list int -> rel.
nums (cons 1 (cons 2 nil)).
words : list string -> rel.
words (cons "a" nil).
?- nums L, len L N.
?- words L, len L N.
```

```output
?- nums L, len L N.
L = cons 1 (cons 2 nil), N = 2.
?- words L, len L N.
L = cons "a" nil, N = 1.
```

## Subtyping

The *subtype* relation `τ ≤ τ'` is the least preorder with

- `c ≤ a` for a constructor `c` of the open type `a`,
- `c ≤ a` for a subtyping edge `c <: a`,
- `a ≤ b` for a refinement `a : type <: b`,
- `τ ≤ τ₁ | … | τₙ` if `τ ≤ τᵢ` for some *i*, and `τ₁ | … | τₙ ≤ τ` if `τᵢ ≤ τ` for every *i*.

The *meet* `τ ⊓ τ'` of two types is the greatest type below both: the smaller of the two if one is a
subtype of the other, and otherwise, for types of facts, the union of their common members. Two base
types or refinements that are not subtypes of each other have no meet, and neither have a base type and
a type of facts.

## Typing of rules

The type of an object variable is the meet of the types of all the columns it occupies in the atoms of
its rule's body, including negated atoms, aggregates and disjunctions. A variable bound only by an
equation `X = t` or an aggregate has the type of `t`, and the result of `count` is an `int`. It is an
error ([E0401](../errors/E0401.md)) if a variable's positions have no meet: no value could occupy all of
them.

Every term must have a subtype of the type its position expects; it is an error
([E0402](../errors/E0402.md)) otherwise. In a head, a variable must have a subtype of the column type.
In a body, a constructor pattern whose fact type is not below the column type can never match, which is
also an error. Base types are never converted into each other: an `int` is not a `float`.

The following rule is rejected, since `X` would have to be both a person and a city.

```hugin,compile_fail,E0401
city : type.
person : type.
lives : person -> city -> rel.
odd : rel.
odd :- lives X _, lives _ X.
```

## Ascriptions

```text
Ascription ::= "(" Expr ":" ObjectType ")"
```

An *ascription* `(t : τ)` states the type of a term. If `t` is not a variable and its type is a subtype
of `τ`, the ascription only fixes the type, as in `(nil : list int)`. Otherwise it is a *checked
downcast*: the term matches only values of type `τ`. A downcast tests the member of a value at run time,
so `τ` must be a type of facts, and the members of `τ` must be members of the type of the position. It is
an error ([E0405](../errors/E0405.md)) otherwise.

The following program selects the students among the members of a union by a downcast.

```hugin,run
person : type.
student : (name : string) -> (years : int) -> person.
teacher : (name : string) -> (subject : string) -> rel.
member : type = student | teacher.
everyone : member -> rel.
everyone (student "ann" 19).
everyone (teacher "cy" "math").
students : student -> rel.
students S :- everyone (S : student).
%output students.
```

```output
students (student "ann" 19).
```
