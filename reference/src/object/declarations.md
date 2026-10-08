# Declarations

A *declaration* introduces a constant with its type. A declaration whose type is an object type, the
type of a relation or the type of a constructor declares an *object constant*; any other declaration
declares a meta constant ([The meta level](../meta/index.md)). This chapter defines the declarations of
object constants. Their types are defined in [Object types](types.md).

## Syntax

```text
Declaration ::= NAME Param* ":" Type ("<:" Type)? ("=" Expr)? "."
Param       ::= VAR | "(" (NAME | VAR) ":" Type ")"
Type        ::= Expr
```

The *head* of a declaration is its name with its parameters. Parameters of object constants are type
parameters of [families](types.md#families); the other declarations have none.

## Classification

The type after `:` decides what a declaration declares:

| declaration | declares |
|---|---|
| `a : type.` | an [open type](types.md#open-types) |
| `a : type <: b.` | a [refinement](types.md#refinements) of the base type or refinement `b` |
| `a : type = τ.` | a [type definition](types.md#type-definitions): `a` stands for `τ` |
| `s : type = { l₁ : τ₁, …, lₙ : τₙ }.` | a *struct*: a relation with the labelled columns `l₁ … lₙ` |
| `r : τ₁ -> … -> τₙ -> rel.` | a *relation* with *n* columns (`r : rel.` has none) |
| `c : τ₁ -> … -> τₙ -> a.` | a *constructor* of the open type `a` with *n* columns |

A *column* is a parameter position of a relation, struct or constructor. The *arity* of the constant is
its number of columns. Every use of a relation or constructor applies it to exactly its arity of
arguments; it is an error ([E0207](../errors/E0207.md)) otherwise.

It is an error ([E0103](../errors/E0103.md)) if a declaration cannot be classified, for example a
function from a meta type to `type`. It is an error ([E0102](../errors/E0102.md)) to declare a name twice
in one scope. A declaration may refer to constants declared later in the file.

## Columns and labels

```text
RelationType    ::= (Column "->")* "rel"
ConstructorType ::= (Column "->")* Type
Column          ::= "(" NAME ":" Type ")" | Type
```

A column may have a *label*: in `edge : (src : node) -> (dst : node) -> rel.` the columns of `edge` are
labelled `src` and `dst`. Labels are used by named patterns, projections and updates
([Records](rules.md#records)), by the `%demand` directive and by measures of `%terminates`. A label
names a column, not a variable. It is an error ([E0307](../errors/E0307.md)) if two columns of a
declaration have the same label.

The last column of a relation may be a [bound column](bound-columns.md), of type `min τ` or `max τ`.

## Relations

A relation `r : τ₁ -> … -> τₙ -> rel` denotes a set of facts `r v₁ … vₙ`. Rules and input facts add
facts to it; a ground rule without a body states one fact.

A relation is also a type: the *fact type* `r`, whose values are the identities of the facts of `r`
([Facts and identity](facts.md)). A column of type `r` holds facts of `r`.

The following program declares a relation of priced items, a relation whose column holds facts of the
first, and a rule that puts every cheap item into it.

```hugin,run
item : (name : string) -> (price : int) -> rel.
item "pen" 2.
item "lamp" 25.
cheap : item -> rel.
cheap I :- item N P, P < 10, I = item N P.
%output cheap.
```

```output
cheap (item "pen" 2).
```

## Constructors

A constructor `c : τ₁ -> … -> τₙ -> a`, where `a` is an open type, builds terms `c t₁ … tₙ` of type
`a`. A constructor without columns, such as `red : color`, is a constant of its type. Every constructor
is also a relation: the term `c v₁ … vₙ` is a fact of `c` once a rule or an input file builds it
([Facts and identity](facts.md)). It is an error ([E0103](../errors/E0103.md)) if the result type of a
constructor is not an open type: a refinement, or the fact type of a struct or relation (its values are
the identities of its facts, which only its own facts have).

The following program declares an open type of shapes with two constructors, builds two shapes and
reads the facts of the constructor `square`.

```hugin,run
shape : type.
circle : (radius : int) -> shape.
square : (side : int) -> shape.
drawn : shape -> rel.
drawn (circle 1).
drawn (square 4).
sides : int -> rel.
sides N :- square N.
%output sides.
```

```output
sides 4.
```

## Structs

A struct `s : type = { l₁ : τ₁, …, lₙ : τₙ }.` declares the relation `s : (l₁ : τ₁) -> … -> (lₙ : τₙ)
-> rel` and its fact type `s`. Its facts are written positionally (`span "a.hgn" 3`) or as a record
(`span { file = "a.hgn", line = 3 }`). A struct with parameters (`pair A B : type = { fst : A, snd : B
}.`) is a [family](types.md#families) of structs.

The following program declares a struct of source positions and uses its fields as labels of a named
pattern.

```hugin,run
span : type = { file : string, line : int }.
span "a.hgn" 3.
span { file = "b.hgn", line = 7 }.
lines : int -> rel.
lines L :- span { line = L, .. }.
%output lines.
```

```output
lines 3.
lines 7.
```

## Order and scope

The declarations of a file form one scope. Within it, a name is declared once; a declaration may be
used before it appears. The [prelude](../prelude.md) is an outer scope: a declaration of the program with
the name of a prelude constant shadows it in the whole file.

The following program declares its own `len` and `list`, which shadow those of the prelude.

```hugin,run
list : type.
nil : list.
len : list -> int -> rel.
len nil 0.
```

```output
len nil 0.
```
