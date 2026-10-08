# Reflection and quoted patterns

*Reflection* represents object syntax as meta data that programs can build, inspect and turn back into
object code. Object code of type `⇑A` ([Staging](meta/staging.md)) is opaque; the *reflective types* of
the prelude are ordinary inductive types whose values describe terms, formulas, rules and items. This
chapter defines the reflective types, the quotes `'{ … }` that turn object syntax into their values
(*reification*), the quoted patterns that match on them, and how data becomes part of the program again
(*reflection*).

Reflection is untyped: the data does not record object types, and reflected code is elaborated and
checked again like code written by hand.

## The reflective types

The prelude declares the following types ([The prelude](prelude.md#reflection)).

| type | constructors | describes |
|---|---|---|
| `seq A` | `snil`, `scons` | sequences; written `[]`, `[a, b]` and `x :: xs` |
| `sym` | none | references to object constants, compared by identity |
| `index` | `izero`, `isuc` | de Bruijn indices of variables bound by aggregates |
| `term` | `tvar string`, `tbound index`, `twild`, `tint int`, `tfloat float`, `tstr string`, `tapp sym (seq term)`, `tarith arith_op term term`, `tneg term` | terms |
| `formula` | `fatom sym (seq term)`, `fcmp cmp_op term term`, `fnot formula`, `fconj formula formula`, `fdisj formula formula`, `fagg agg_op term term formula` | formulas |
| `rule` | `horn (seq formula) (seq formula)` | a rule: its heads and its body conjuncts |
| `item` | `irule rule`, `iquery (seq formula)`, `inamed string rule`, `ierror string`, `irelation sym (seq column)` | items |
| `module` | (a definition: `seq item`) | the rules and queries of a file |
| `column` | `colof sym index` | the column of an object constant at an index |

`arith_op`, `cmp_op` and `agg_op` enumerate the operators `+ - * / ^`, the comparisons and the
aggregates. An object variable is represented by its name (`tvar "X"`). In an aggregate
`X = k { t | φ }` whose term `t` is a variable `V`, `V` is bound by the aggregate: its occurrences in `t`
and `φ` are `tbound` indices (a locally nameless representation). `fagg k x t φ` holds the result `x`,
the term `t` and the body `φ`.

A program may declare its own types with these names; the compiler finds the reflective types in the
prelude's scope, not in the program's.

## Lists

```text
List    ::= "[" (Expr ("," Expr)*)? "]"
Cons    ::= Expr "::" Expr
```

`[e₁, …, eₙ]` is the sequence of the elements, `e :: es` the sequence with first element `e`. A `[`
starts a list unless it has the shape of a lambda `[x] e`.

## Quotes

```text
Quote   ::= "'{" (Entry ("." Entry)* "."?)? "}"
Entry   ::= RuleName? Expr (":-" Formula)? | "?-" Formula
```

A *quote* `'{ … }` holds object syntax as data, written as in a file: its content is a sequence of
entries (rules, facts and queries) separated by periods, the last period optional. The `'` must be
directly followed by `{`; a prime inside or after a name is part of the name (`x'`). Which data a quote
denotes depends on the reflective type expected where it stands, which gives the *category* of its
content:

| expected type | content | example |
|---|---|---|
| `module`, `seq item` | items, each with its period | `'{ edge 1 2. path X Y :- edge X Y. }` |
| `seq rule` | rules, each with its period | `'{ p X :- q X. r 1. }` |
| `item` | one rule, named rule (`inamed`) or query (`iquery`) | `'{ @step path X Z :- path X Y, edge Y Z }` |
| `rule` | one rule; a fact is a rule without body | `'{ path X Y :- edge X Y }`, `'{ edge 1 2 }` |
| `formula` | a formula, without `:-` or period | `'{ edge X Y, not p X }` |
| `term` | a term | `'{ f X 1 }`, `'{ N + 1 }` |
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

Meta values are written as holes (see below): `'{ $R X :- $..Body }`. It is an error
([E0917](errors/E0917.md)) to quote `as`, an ascription, a projection or an update, which have no
representation, or content of another category than the expected type's (two items where a rule is
expected, a rule where a formula is expected). A quote where no reflective type is expected (the type is
another one, or it is not known, as for a definition without a declared type) is an error
([E0919](errors/E0919.md)): ascribe it, `('{ p X } : formula)`, or declare the type. An item `$e.` expects
reflected items, so `$'{ … }.` needs no ascription. Object syntax outside a quote is never data: the
arguments of directives are the exception, as they are object syntax themselves; an argument at a
parameter of a reflective type is quoted implicitly ([Directives](directives.md)).

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
sequence. In a pattern, `$X` binds the meta variable `X` to the data at its place, `$_` matches anything,
and `$..Xs` binds the rest of a sequence and must end it. It is an error ([E0917](errors/E0917.md)) if a
hole is in a place it cannot stand for.

## Quoted patterns

A clause pattern whose argument has a reflective type may be a quote: a *quoted pattern*, with the
syntax and the categories of quotes in expressions. It is elaborated to a pattern over the constructors of the reflective types, so
[coverage](meta/coverage.md) and [termination](meta/termination.md) apply unchanged.

- An object constant in a quoted pattern matches that constant by identity. A pattern on `edge` does not
  match the `edge` of a module `m.edge`, nor a relation `edge` that shadows the one in scope where the
  pattern is written. Literals match by value.
- A plain uppercase variable matches any object variable; patterns are linear, so two occurrences are
  not compared. `_` in a term position matches the wildcard, and in a formula position anything.
- A higher-order hole `$F[V]` in a pattern matches a formula (or a term) that may mention the variable
  `V` bound by an enclosing aggregate; it binds `F : term -> formula` (or `term -> term`), the function
  that puts its argument in the place of `V`.

Splitting on object constants and literals has a branch for each value that the clauses name and a
default branch for the clauses that do not constrain the argument.

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

## Reflecting data into the program

```text
SpliceItem ::= "$" Expr "."
```

An item `$e.`, where `e` has type `rule`, `item`, `seq rule` or `module`, stands for the rules, queries and
declarations that `e` evaluates to: it is the staging splice applied to reflected data. `$f a.` is read
as `$(f a).`; a quote or a list in `$e.` is checked against `module` (`$'{ p 1. }.`). The data is evaluated during
elaboration, turned into syntax whose object constants are already resolved, and elaborated and checked
like a hand-written item, at the object level too (typing, stratification, termination). It is an error
([E0918](errors/E0918.md)) if the data is not closed (it depends on a postulate or on a parameter of a
meta function) or does not describe object code (a variable without a name, a rule without heads, a
bound index outside its aggregate).

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
(`'{ edge }`). Symbols have no constructors; they are compared by
identity. The prelude declares four primitive operations on symbols and literals:

| primitive | meaning |
|---|---|
| `same : A -> A -> bool` | whether two symbols or two literals are equal |
| `labels : sym -> seq string` | the labels of the columns of a constant, `""` for a column without one |
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
