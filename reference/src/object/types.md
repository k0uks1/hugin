# Object types

An *object type* classifies the values of the object level. The object types are the elements of the
universe `type`. This chapter defines the object types, the subtype relation between them, families of
object constants, the typing of object code and where it is typed.

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

- the constructors whose result type is `a`,
- the relations, structs and constructors `c` with a *subtyping edge* `c <: a.`, and
- the members of every open type `b` with a subtyping edge `b <: a.`

```text
SubtypeEdge ::= Expr "<:" Expr "."
```

A value of type `a` is the identity of a fact of one of the members. It is an error
([E0404](../errors/E0404.md)) if the left side of an edge is not a fact type or an open type, or if the
right side is not an open type. The error is reported at the edge.

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

The following program makes every pet an animal by an edge between two open types. The constructor
`dog` of `pet` is then a member of `animal`.

```hugin,run
animal : type.
pet : type.
pet <: animal.
dog : (name : string) -> pet.
zoo : animal -> rel.
zoo (dog "rex").
?- zoo A.
```

```output
?- zoo A.
A = dog "rex".
```

## Fact types

Every relation, struct and constructor `c` is also a type, the *fact type* `c`. Its values are the
identities of the facts of `c` ([Facts and identity](facts.md)). A fact type is a subtype of the open
type of its constructor and of every open type it has an edge to.

## Unions

A *union* `τ₁ | … | τₙ` is the type of the values of any of its members. The members of a union are
*types of facts* (open types, fact types and unions of them), and no two of them have a common member. It
is an error ([E0404](../errors/E0404.md)) if a column of a relation, struct or constructor has a union
type that breaks this rule; the error is reported at the declaration of the column. A type is *closed* if
it is a fact type or a union of closed types. Projections and updates apply only to closed types
([Records](rules.md#records)), since a closed type has a known set of members.

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

The object side of a [shared data type](../meta/families.md#shared-data), such as the prelude's `list`
(declared `list A : data.`), is a family of types and constructors of this kind.

The application of a family to object types is an *instance*. Two applications to the same types are the
same instance: `list int` in two places is one type, and `len` used at lists of integers is one
relation. Instances are named after their arguments, `list[int]` and `len[int]`, in diagnostics and in
the output of `--print-after`; facts and query answers show the name of the family.

The type arguments of a use of a family are inferred from the types of the terms around it, including
the type that the [typing of rules](#typing-of-rules) finds for a variable. It is an error
([E0206](../errors/E0206.md)) if nothing determines them; an ascription such as `(nil : list int)`
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

In the following query only the typing of rules determines the type argument of `cons`: `V` is bound by
the projection `S.price` over the union `pen | ink`, whose type is `int`, so `cons V nil` is a
`list int`.

```hugin,run
pen : type = { price : int }.
ink : type = { price : int }.
stock : (s : pen | ink) -> rel.
pen 3. ink 5.
stock P :- (pen _ as P).
stock P :- (ink _ as P).
prices : (l : list int) -> rel.
prices (cons 3 nil).
?- stock S, V = S.price, L = cons V nil, prices L.
```

```output
?- stock S, V = S.price, L = cons V nil, prices L.
S = pen 3, V = 3, L = cons 3 nil.
```

## Subtyping

The *subtype* relation `τ ≤ τ'` is the least preorder with

- `c ≤ a` for a constructor `c` of the open type `a`,
- `c ≤ a` for a subtyping edge `c <: a`,
- `a ≤ b` for a refinement `a : type <: b`,
- `τ ≤ τ₁ | … | τₙ` if `τ ≤ τᵢ` for some *i*, and `τ₁ | … | τₙ ≤ τ` if `τᵢ ≤ τ` for every *i*.

Two instances of a family are related only if they are the same instance: `list var` is not a subtype of
`list expr`, whatever `var` and `expr` are.

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

*Spliced code*, a meta value of type `⇑τ` inserted into object code ([Staging](../meta/staging.md)), is a
term of type `τ` whose shape is not known. In a head, `τ` must be a subtype of the column type `σ`. In a
body, `τ` and `σ` must have a meet. It is an error ([E0402](../errors/E0402.md)) otherwise.

The following rule is rejected, since `X` would have to be both a person and a city.

```hugin,compile_fail,E0401
city : type.
person : type.
lives : person -> city -> rel.
odd : rel.
odd :- lives X _, lives _ X.
```

## Where object code is typed

The rules of this chapter apply to object code wherever it is written. The compiler types object code
during elaboration. Each of the following is typed as a whole, once it is elaborated:

- a rule or a query, in a file, in a module body or reflected from data;
- a clause of a [formula function](../meta/staging.md#formula-functions) defined by rules;
- the right-hand side of a meta definition with a declared type (`x : A = e.`, `f params : A = e.`) or of
  a clause of a meta function: the object code that the right-hand side is, inside the parameters of the
  definition, and the object code that it passes to the meta functions it applies, at their parameter
  types;
- a [quote](../reflection.md#quotes) `'{ … }`.

Each of these is typed whether or not anything uses it, so a meta function whose right-hand side can
build ill-typed object code is rejected where it is defined. Object code in other places of meta code,
such as a field of a record value or a definition of a [`where`](../meta/where.md) block, is typed only
after staging, in the items that use it (see below).
In a quote, the occurrences of one hole of type `quoted A` in a body are one variable for the meet
([Quotes](../reflection.md#quotes)).

The following formula function is rejected where it is defined, although nothing uses it: `lit N` is an
`expr`, in a column of type `typ`.

```hugin,compile_fail,E0402
expr : type. typ : type.
lit : int -> expr.
tint : typ.
typed : (e : expr) -> (t : typ) -> rel.
check : int -> prop.
check N = typed (lit N) (lit N).
```

The following function is rejected where it is defined: it puts its argument of type `⇑typ` in a column
of type `expr`.

```hugin,compile_fail,E0402
expr : type.
typ : type.
typed : (e : expr) -> (t : typ) -> rel.
swap : ⇑expr -> ⇑typ -> ⇑prop.
swap E T = typed T E.
```

The following formula function is accepted: its argument of type `⇑expr` stands in a body column of
type `var`, and `expr` and `var` meet.

```hugin,run
expr : type.
var : type.
var <: expr.
x : var.
declared : (v : var) -> rel.
seen : (e : expr) -> rel.
record : ⇑expr -> ⇑prop.
record E = declared E.
seen x.
declared x.
used : (e : expr) -> rel.
used E :- seen E, record E.
?- used E.
```

```output
?- used E.
E = x.
```

### Functor bodies

The body of a [functor](../modules.md#functors) is typed once, for every argument. In the body, an
object type that the functor's parameter gives, such as `g.node` for the parameter `g`, is *abstract*:
it is a subtype only of itself, and a subtyping edge cannot make it a member of an open type
([E0404](../errors/E0404.md)). The following checks are decided in the body:

- a term in a head column must have a subtype of the column type;
- a constructor term must have a fact type below the type of its column;
- spliced code must fit its column, as stated above.

The following checks involve what an abstract type is, and are made for each instance of the body, with
the note "in application of" the functor:

- a meet that involves an abstract type ([E0401](../errors/E0401.md));
- a comparison, arithmetic, a unary minus or an aggregate over a term of an abstract type, and a literal
  in a column of an abstract type ([E0402](../errors/E0402.md));
- an ascription that involves an abstract type ([E0405](../errors/E0405.md));
- a projection or an update of a variable of an abstract type ([E0303](../errors/E0303.md),
  [E0304](../errors/E0304.md), [E0305](../errors/E0305.md)).

The following functor is rejected at its body: `X` has the abstract type `g.node`, which is not a
subtype of `expr`, whatever the functor is applied to.

```hugin,compile_fail,E0402
graph_sig : Type = { node : type, edge : node -> node -> rel }.
expr : type.
lit : int -> expr.
loops (g : graph_sig) = {
  out : (x : expr) -> rel.
  out X :- g.edge X X.
}.
```

The following program is rejected at its second instance: `X < Y` compares two values of the abstract
type `g.node`, which is `int` in the first instance and `place` in the second.

```hugin,compile_fail,E0402
graph_sig : Type = { node : type, edge : node -> node -> rel }.
rising (g : graph_sig) = {
  up : (x : g.node) -> (y : g.node) -> rel.
  up X Y :- g.edge X Y, X < Y.
}.
hop : int -> int -> rel.
place : type. home : place. work : place.
road : place -> place -> rel.
ints = rising { node = int, edge = hop }.
places = rising { node = place, edge = road }.
```

### Staged items

After [staging](../meta/staging.md), every staged rule and query is typed again, by the same rules,
since its variables may meet types that its source did not show: the columns in which the code of a
formula function or a meta function uses its arguments, and the instances of families and module
bodies. A problem is reported only for an item that involves meta code:

- an item of a module instance;
- an instance of a rule of a family that is generic over its type arguments;
- an item reflected from data or added by a directive;
- an item whose object code contains spliced code, a lifted meta value or an application of a formula
  function.

An item without meta code was typed as it is written.

The following rule is rejected after staging: `isVar X` stages to `vars X`, so `X` is a `num` and a
`var`, which have no common member.

```hugin,compile_fail,E0401
expr : type.
num : (n : int) -> expr.
var : (name : string) -> expr.
vars : (v : var) -> rel.
nums : (n : num) -> rel.
isVar : ⇑expr -> ⇑prop.
isVar E = vars E.
odd : rel.
odd :- nums X, isVar X.
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
