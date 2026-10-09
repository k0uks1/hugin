# Reflection and quoted patterns

*Reflection* represents object syntax as meta data that programs can build, inspect and turn back into
object code. Object code of type `⇑A` ([Staging](meta/staging.md)) is opaque; the *reflective types* of
the prelude are ordinary inductive families whose values describe terms, formulas, rules and items. This
chapter defines the reflective types, the quotes `'{ … }` that turn object syntax into their values
(*reification*), the quoted patterns that match on them, and how data becomes part of the program again
(*reflection*).

The reflective types are untyped: the data does not record object types. A quote is
[object-typed](object/types.md#where-object-code-is-typed) where it is written, and `quoted A` is a term
of the object type `A` (see [Typed terms](#typed-terms)). Reflected code is elaborated and checked again
like code written by hand.

## The reflective types

The prelude declares the following types ([The prelude](prelude.md#reflection)).

| type | constructors | describes |
|---|---|---|
| `list A` | `nil`, `cons` | sequences: the prelude's shared `list` ([Inductive families](meta/families.md#shared-data)) at the meta level, written `[]`, `[a, b]` and `x :: xs` |
| `sym` | none | references to object constants, compared by identity |
| `index` | `izero`, `isuc` | de Bruijn indices of variables bound by aggregates |
| `term` | `tvar string`, `tbound index`, `twild`, `tint int`, `tfloat float`, `tstr string`, `tapp sym (list term)`, `tarith arith_op term term`, `tneg term` | terms |
| `formula` | `fatom sym (list term)`, `fcmp cmp_op term term`, `fnot formula`, `fconj formula formula`, `fdisj formula formula`, `fagg agg_op term term formula` | formulas |
| `rule` | `horn (list formula) (list formula)` | a rule: its heads and its body conjuncts |
| `item` | `irule rule`, `iquery (list formula)`, `inamed string rule`, `ierror string`, `irelation sym (list column)` | items |
| `module` | (a definition: `list item`) | the rules and queries of a file |
| `column` | `colof sym index` | the column of an object constant at an index |
| `quoted A` | `qterm term` | a term of the object type `A` ([Typed terms](#typed-terms)) |

`arith_op`, `cmp_op` and `agg_op` enumerate the operators `+ - * / ^`, the comparisons and the
aggregates. An object variable is represented by its name (`tvar "X"`). In an aggregate
`X = k { t | φ }` whose term `t` is a variable `V`, `V` is bound by the aggregate: its occurrences in `t`
and `φ` are `tbound` indices (a locally nameless representation). `fagg k x t φ` holds the result `x`,
the term `t` and the body `φ`.

A program may declare its own types with these names. The compiler finds the reflective types in the
prelude's scope, not in the program's.

## Lists

```text
List    ::= "[" (Expr ("," Expr)*)? "]"
Cons    ::= Expr "::" Expr
```

`[e₁, …, eₙ]` is the list of the elements, `e :: es` the list with first element `e`: `cons` and `nil` of
the prelude's `list`, at the stage of the position. In meta code it is a meta list; in object code and
inside a quote it is the object list (`[X, Y]` in a rule head is the term `cons X (cons Y nil)`). A `[`
starts a list unless it has the shape of a lambda `[x] e`.

## Quotes

```text
Quote   ::= "'{" (Entry ("." Entry)* "."?)? "}"
Entry   ::= RuleName? Expr (":-" Formula)? | "?-" Formula
```

A *quote* `'{ … }` holds object syntax as data, written as in a file: its content is a sequence of
entries (rules, facts and queries) separated by periods, the last period optional. Like the items of a
module body, an entry does not start in column 0: a quote over several lines indents its entries. The
`'` must be directly followed by `{`; a prime inside or after a name is part of the name (`x'`). Which
data a quote denotes depends on the reflective type expected where it stands, which gives the *category*
of its content:

| expected type | content | example |
|---|---|---|
| `module`, `list item` | items, each with its period | `'{ edge 1 2. path X Y :- edge X Y. }` |
| `list rule` | rules, each with its period | `'{ p X :- q X. r 1. }` |
| `item` | one rule, named rule (`inamed`) or query (`iquery`) | `'{ @step path X Z :- path X Y, edge Y Z }` |
| `rule` | one rule; a fact is a rule without body | `'{ path X Y :- edge X Y }`, `'{ edge 1 2 }` |
| `formula` | a formula, without `:-` or period | `'{ edge X Y, not p X }` |
| `term` | a term | `'{ f X 1 }`, `'{ N + 1 }` |
| `quoted A` | a term of type `A` | `'{ cons 1 nil }` as a `quoted (list int)` |
| `sym` | the name of an object constant | `'{ edge }` |
| `decl` | the name of an object constant, or a rule name | `'{ edge }`, `'{ @step }` |
| `measure` | a measure of `%terminates` | `'{ (X, Y) }` |

In the content,

- an object constant (also a path `m.r`) or a hole applied to arguments is an atom or a term;
- a variable or parameter whose type is object code of a relation or constructor type
  (`R : ⇑(A -> rel)`, a functor's parameter `g.edge`) stands for that constant, like a name;
- `,`, `;`, `not`, comparisons and aggregates are formulas, arithmetic and literals terms;
- a named pattern `r { l = t, .. }` is the atom with its arguments in column order;
- a plain uppercase identifier is an object variable (`tvar "X"`), and `_` the wildcard `twild`.

A quote is object-typed where it is written, by the rules of [Object types](object/types.md): each rule
of its content is typed like a rule of the program, a formula like a body, and a term at the type the
expected `quoted A` gives (at no type for `term`). Its holes have the types of their values: a hole of
type `quoted A` is a term of type `A`, a hole of type `term` a term of any type, and a meta value of a
base or shared type a term of the type it lifts to. It is an error ([E0402](errors/E0402.md),
[E0401](errors/E0401.md)) if the content is ill-typed, whether or not the quote is ever reflected.

A variable `X` of type `quoted A` that is a hole `$X` at several places of the body of one quoted rule,
query or formula is one object variable there: its type is the meet of the types of these positions and
of `A`, as for a variable of a rule. It is an error ([E0401](errors/E0401.md)) if the meet is empty,
since the data in the hole may be a variable. In a head, `$X` is a term of type `A`, as above.

The following generator is rejected where it is defined: a value that the hole `$X` holds would have to
be both a `teacher` and a `janitor`.

```hugin,compile_fail,E0401
staff : type.
teacher : (name : string) -> staff.
janitor : (name : string) -> staff.
teaches : teacher -> rel.
cleans : janitor -> rel.
busy : rel.
both : quoted staff -> rule.
both X = '{ busy :- teaches $X, cleans $X }.
```

Meta values are written as holes (see below): `'{ $R X :- $..Body }`. It is an error
([E0917](errors/E0917.md)) to quote `as`, an ascription, a projection or an update, which have no
representation, or content of another category than the expected type's (two items where a rule is
expected, a rule where a formula is expected). It is an error ([E0919](errors/E0919.md)) if a quote
stands where no reflective type is expected: the expected type is another one, or it is not known, as for
a definition without a declared type. Ascribe the quote, `('{ p X } : formula)`, or declare the type. An
item `$e.` expects reflected items, so `$'{ … }.` needs no ascription. Object syntax outside a quote is
never data: the arguments of directives are the exception, as they are object syntax themselves; an
argument at a parameter of a reflective type is quoted implicitly ([Directives](directives.md)).

The following program builds a module as data and reflects it into the program.

```hugin,run
edge : int -> int -> rel.
path : int -> int -> rel.
rules : module = '{
  edge 1 2.
  edge 2 3.
  path X Y :- edge X Y.
  path X Z :- edge X Y, path Y Z.
}.
$rules.
?- path 1 Z.
```

```output
?- path 1 Z.
Z = 2.
Z = 3.
```

## Holes

```text
Hole ::= "$" Expr | "$" ".." Expr | "$" Expr "[" Expr ("," Expr)* "]"
```

A *hole* marks a place in a quote where a meta value stands. Holes exist only inside a quote; outside,
`$e` is the splice of [staging](meta/staging.md), and `$..` and `$F[…]` are errors
([E0917](errors/E0917.md)).

- `$X` is a single value: a term, a formula, a symbol in the place of a relation. A hole that is a whole
  entry (`'{ $R }`, `'{ edge 1 2. $I. }`) is a value of the entry's kind (a rule, an item); in an
  expression it may also be a formula (the fact) or, for an item, a rule.
- `$..Xs` is a sequence: the arguments of an atom, the heads or the body conjuncts of a rule, or the
  entries of a module.
- `$F[t₁, …, tₙ]` is a *higher-order hole*: `F` applied to object terms. The `[` follows `F` directly,
  without a space.

In an expression, a hole splices a value into the quoted syntax; a sequence hole may be anywhere in its
sequence. A hole `$e` at a term whose value is not `term` data but a meta value of a base type or of a
[shared data type](meta/families.md#shared-data) stands for the value's *reification*: `tint e`,
`tfloat e` or `tstr e` for a base type, `T.reify ḡ e` for a shared type, with the element functions given
by the type. The reified data describes exactly the object code that the value
[lifts](meta/staging.md#lifting) to, so reflecting `'{ p $e }` gives the rule `p e` with `e` lifted.
There is no such conversion in patterns. In a pattern, `$X` binds the pattern variable `X` to the data at
its place, `$_` matches anything, and `$..Xs` binds the rest of a sequence and must end it. It is an
error ([E0917](errors/E0917.md)) if a hole is in a place it cannot stand for.

The following program generates one fact per suffix of a compile-time list. The hole `$(X :: Xs)` is a
meta list, so its reification `list.reify tint (X :: Xs)` is inserted.

```hugin,run
held : list int -> rel.
suffixes : list int -> list rule.
suffixes [] = [].
suffixes (X :: Xs) = '{ held $(X :: Xs) } :: suffixes Xs.
$suffixes [1, 2].
?- held L.
```

```output
?- held L.
L = cons 1 (cons 2 nil).
L = cons 2 nil.
```

## Quoted patterns

A clause pattern whose argument has a reflective type may be a quote: a *quoted pattern*, with the
syntax and the categories of quotes in expressions. It is elaborated to a pattern over the constructors
of the reflective types, so [coverage](meta/coverage.md) and [termination](meta/termination.md) apply
unchanged.

- An object constant in a quoted pattern matches that constant by identity. A pattern on `edge` does not
  match the `edge` of a module `m.edge`, nor a relation `edge` that shadows the one in scope where the
  pattern is written. Literals match by value.
- A plain uppercase variable matches any object variable; patterns are linear, so two occurrences are
  not compared. `_` in a term position matches the wildcard, and in a formula position anything.
- A higher-order hole `$F[V]` in a pattern matches a formula (or a term) that may mention the variable
  `V` bound by an enclosing aggregate; it binds `F : term -> formula` (or `term -> term`), the function
  that puts its argument in the place of `V`.

- A hole `$X` at an argument of an object constant whose column has a base type or the type of a
  constant binds `X : quoted τ`, a term of the column's type `τ`: in `typed $E $G $T`, `E` is a
  `quoted expr`. Other holes bind data of their category (`term`, `formula`, a list for `$..Xs`).

Splitting on object constants and literals has a branch for each value that the clauses name and a
default branch for the clauses that do not constrain the argument. The type of a hole is not checked when
data is matched: data built without a quote (by constructors, or by `qterm`) may describe an ill-typed
term, which is found when the data is reflected.

The following function swaps the arguments of every binary atom; `$R` matches the relation as a symbol.

```hugin,run
node : type. a : node. b : node.
edge : node -> node -> rel.
flip : formula -> formula.
flip '{ $R $X $Y } = '{ $R $Y $X }.
flip F = F.
$'{ $(flip '{ edge a b }). }.
%output edge.
```

```output
edge b a.
```

The following function restricts the count of a rule to the items that are not excluded. `$F[V]`
matches the body of the aggregate, which mentions the variable `V` bound by the aggregate.

```hugin,run
item : type. pen : item. ink : item. cap : item.
stock : item -> rel.
excluded : item -> rel.
count_ok : int -> rel.
restrict : rule -> rule.
restrict '{ count_ok $X :- $Y = count { V | $F[V] } } = '{ count_ok $X :- $Y = count { V | $F[V], not excluded V } }.
restrict R = R.
$restrict '{ count_ok N :- N = count { I | stock I } }.
stock pen. stock ink. stock cap.
excluded cap.
%output count_ok.
```

```output
count_ok 2.
```

## Typed terms

`quoted A` is a term of the object type `A`: a quote checked against `quoted A` is one, and so is a hole
of a quoted pattern at a column of type `A`. Its value is the data `qterm t` with the `term` `t`; the
prelude's `raw : quoted A -> term` gives `t` back. A `quoted A` is accepted where a `term` is expected
(`raw` is inserted), where a `quoted B` is expected if `A` is a subtype of `B`, and in object code, where
it stands for its term. `qterm` makes a `quoted A` from any `term` without a check.

The following function guards the rules of `typed` whose expression is a negation. `E` is a
`quoted expr`, so the quotes that use it are checked where `guard` is defined: `'{ asked $G $E }` would
be an error.

```hugin,run
expr : type. typ : type. ctx : type.
lit : int -> expr.
neg : expr -> expr.
tint : typ.
empty : ctx.
typed : (e : expr) -> (g : ctx) -> (t : typ) -> rel.
asked : (e : expr) -> (g : ctx) -> rel.
guard : rule -> list rule.
guard '{ typed (neg $E) $G $T :- $..B } = ['{ typed (neg $E) $G $T :- asked (neg $E) $G, $..B }, '{ asked $E $G :- asked (neg $E) $G }].
guard R = [R].
$guard '{ typed (neg E) G tint :- typed E G tint }.
typed (lit N) G tint :- asked (lit N) G, N = 1.
asked (neg (lit 1)) empty.
?- typed X empty T.
```

```output
?- typed X empty T.
X = lit 1, T = tint.
X = neg (lit 1), T = tint.
```

### Typed atoms

A *typed atom* is a `quoted A` whose type `A` is a [type of facts](object/types.md#unions): facts are
terms, so a term of the fact type `edge` is an atom of `edge`. A `quoted A` is accepted where a `formula`
is expected if `A` is a type of facts, and the prelude's primitive `qatom : quoted A -> formula` is
inserted. `qatom` turns the data `qterm (tapp s ts)` into the atom `fatom s ts`. So a typed atom stands
in a quote as a head, a formula of a body, a fact or an item. It is an error ([E0901](errors/E0901.md)) if
`A` is not a type of facts, such as a base type.

A quote checked against `quoted A` is checked at the positions of a head, so a typed atom that it builds
fits both a head and a body. `qatom` applied to the data of another term than an application, which only
`qterm` can build, stays unevaluated; it is an error ([E0918](errors/E0918.md)) to reflect it.

The following program builds the atoms of `edge` and `path` with generators that are checked where they
are defined, and uses them as facts, in a head, in a body and under `not`.

```hugin,run
node : type. a : node. b : node. c : node.
edge : node -> node -> rel.
path : node -> node -> rel.
closed : node -> rel.
link : quoted node -> quoted node -> quoted edge.
link X Y = '{ edge $X $Y }.
reach : quoted node -> quoted node -> quoted path.
reach X Y = '{ path $X $Y }.
x : quoted node = qterm (tvar "X").
y : quoted node = qterm (tvar "Y").
$'{ $(link '{ a } '{ b }). $(link '{ b } '{ c }). }.
closed b.
$'{ $(reach x y) :- $(link x y), not closed $x. }.
%output path.
```

```output
path a b.
```

The following quote is rejected: `int` is not a type of facts, so a `quoted int` is not an atom.

```hugin,compile_fail,E0901
size : quoted int = '{ 3 }.
bad : formula = '{ $size }.
```

## Reflecting data into the program

```text
SpliceItem ::= "$" Expr "."
```

An item `$e.`, where `e` has type `rule`, `item`, `list rule` or `module`, stands for the rules, queries
and declarations that `e` evaluates to: it is the staging splice applied to reflected data. `$f a.` is
read as `$(f a).`; a quote or a list in `$e.` is checked against `module` (`$'{ p 1. }.`). The data is
evaluated during elaboration, turned into syntax whose object constants are already resolved, and
elaborated and checked like a hand-written item, at the object level too (typing, stratification,
termination). It is an error ([E0918](errors/E0918.md)) if the data is not closed, because it depends on
a postulate or on a parameter of a meta function. It is also an error if the data does not describe
object code, such as a variable without a name, a rule without heads or a bound index outside its
aggregate.

Generated items take the place of the item `$e.`. A diagnostic in a generated item points at the syntax
the data was quoted from, with a note "in code reflected by `$e`". A query generated by `$e.` prints the
text of the item `$e.`.

An item `$e.` is allowed at the top level of a file only; in a module body it is an error
([E0907](errors/E0907.md)).

In object code, a meta value of type `formula` or `term` stands for the formula or term it describes,
with or without `$`. Its variables are the variables of the rule with the same names.

The following program uses a formula and a term as data in rules.

```hugin,run
p : int -> rel.
q : int -> rel.
r : int -> int -> rel.
body : formula = '{ q X, X > 1 }.
three : term = '{ 1 + 2 }.
q 1. q 2. q 3.
p X :- $body.
r X $three :- body.
%output p. %output r.
```

```output
p 2.
p 3.
r 2 3.
r 3 3.
```

## Symbols and derived constants

A *symbol* is a value of type `sym`: a reference to an object constant, written as a quote of its name
(`'{ edge }`). Symbols have no constructors; they are compared by identity. The prelude declares four
primitive operations on symbols and literals:

| primitive | meaning |
|---|---|
| `same : A -> A -> bool` | whether two symbols or two literals are equal |
| `labels : sym -> list string` | the labels of the columns of a constant, `""` for a column without one |
| `derive : sym -> string -> sym` | the constant `r.l` *derived* from `r` with the label `l` |
| `derived : sym -> bool` | whether a symbol is a derived constant |

A primitive reduces when its arguments are closed; otherwise its application stays unevaluated.

A *derived constant* `r.l` is created on the first use of `derive r "l"`, once per constant and label, so
its name is stable and cannot capture a name of the program. It is declared by the item
`irelation (derive r "l") cols`: a relation with the columns `cols`, each a column `colof s k` of an
existing constant with its label and type. A derived relation of a family's columns is a family with the
same parameters. It is an error ([E0918](errors/E0918.md)) to refer to a derived constant that no item
declares.

The following program declares the reverse of a relation as a derived relation, with a rule and a query
for it.

```hugin,run
node : type. a : node. b : node.
edge : (src : node) -> (dst : node) -> rel.
edge a b.
reversed : sym -> module.
reversed R = irelation (derive R "rev") [colof R 1, colof R 0] :: '{
  $(derive R "rev") Y X :- $R X Y.
  ?- $(derive R "rev") Y X.
}.
$reversed '{ edge }.
```

```output
$reversed '{ edge }.
Y = b, X = a.
```
