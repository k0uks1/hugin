# Lexical structure

A Hugin source file is a sequence of Unicode characters in UTF-8. The lexer divides it into *tokens*,
which the parser groups into items. This chapter defines the tokens, the comments, the items and the
precedence of operators. Facts files (see [Input facts](object/io.md#input-facts)) use the same tokens.

## Whitespace and comments

Spaces, tabs and line breaks separate tokens and have no other meaning, with one exception: an
argument, the operand of a prefix operator, the body of a lambda, and the formula after `?-` or `:-`,
cannot start in column 0 of a line (see [Items](#items)).

A *comment* starts with `(*` and ends with the matching `*)`. Comments nest: `(* a (* b *) c *)` is one
comment. It is an error ([E0002](errors/E0002.md)) if a comment is not closed before the end of the file.

## Identifiers and variables

```text
NAME      ::= LOWER IDCHAR*
VAR       ::= (UPPER | "_") IDCHAR*
IDCHAR    ::= LETTER | DIGIT | "_" | "'"
```

`LETTER`, `LOWER`, `UPPER` and `DIGIT` are the ASCII letters, lowercase letters, uppercase letters and
digits. An identifier is a maximal sequence of `IDCHAR`s that starts with a letter or `_`.

The case of the first character decides the class of an identifier:

- A *name* (`NAME`) starts with a lowercase letter. Names refer to constants: types, relations,
  constructors, functions, modules and labels (`edge`, `typed`, `x'`).
- A *variable* (`VAR`) starts with an uppercase letter or `_`. Variables of rules and queries are
  *object variables*. Variables in clauses and in the types of declarations are variables of meta code
  (`X`, `Body`, `_rest`).
- The variable `_` alone is the *wildcard*. Each occurrence of `_` is a variable of its own that occurs
  nowhere else.

The identifier `Type` is lexically a variable. It names the universe of meta types (see
[Universes](meta/universes.md)).

It is an error ([E0004](errors/E0004.md)) to declare a constant with a variable as its name.

> **Rationale.** The convention follows Prolog and Twelf: in a rule such as `path X Z :- edge X Y, path Y
> Z.` the variables need no declaration.

## Keywords

The following names are *keywords*. They cannot be used as names of constants.

```text
type   rel   prop   not   as   with   count   sum   min   max   where
match   rewrite
```

`in` is a *contextual keyword*: it ends the equation of [`rewrite h in e`](meta/match.md#rewrite) and is
an ordinary name everywhere else, so a relation `in X S` or a meta function `in` may be declared. In the
equation of a `rewrite`, a name `in` is written in parentheses: `rewrite f (in X) in e`.

`min` and `max` are keywords in two roles: before `{` they start an aggregate, otherwise they start a
[bound column](object/bound-columns.md) type `min τ`.

## Directive and rule names

```text
DIRECTIVE ::= "%" LOWER IDCHAR*
RULE_NAME ::= "@" LOWER IDCHAR*
```

A *directive name* `%d` starts a [directive](directives.md) or one of the forms `%builtin`, `%import`,
`%use`, `%export`, `%infix` and `%complete`. A *rule name* `@r` names a rule (see
[Rules](object/rules.md#named-rules)).
It is an error ([E0001](errors/E0001.md)) if `%` or `@` is not followed by a lowercase letter.

## Literals

```text
INT       ::= DIGIT+
FLOAT     ::= DIGIT+ "." DIGIT+ (("e" | "E") ("+" | "-")? DIGIT+)?
STRING    ::= '"' (CHAR | ESCAPE)* '"'
ESCAPE    ::= '\"' | '\\' | '\n' | '\t' | '\u{' HEXDIGIT+ '}'
```

An *integer literal* denotes a 64-bit signed integer of the object level, a numeral of a nat-like meta
family, or a meta integer. It is an error ([E0003](errors/E0003.md)) if its value is larger than
2⁶³ − 1, unless it is checked against a nat-like family, whose numerals are unbounded ([Inductive
families](meta/families.md#numerals)), or is a meta integer, which is unbounded as well
([`std/int`](std/int.md)); the literal `9223372036854775808` is also valid after a unary minus.

A *float literal* denotes a 64-bit IEEE 754 number. It has digits on both sides of the point: `1.0`,
`2.5e-3`. The text `1.` is the integer `1` followed by a period.

A *string literal* is enclosed in double quotes and cannot span lines. Its escapes stand for a double
quote, a backslash, a line feed, a tab and the Unicode code point with the given hexadecimal number. It
is an error ([E0003](errors/E0003.md)) to use another escape or a code point that is not a Unicode
scalar value, and ([E0002](errors/E0002.md)) to leave a string unterminated.

There is no literal for negative numbers. `-5` is the unary minus applied to `5`; the parser folds it
into the literal −5.

The type of a literal is given by its position. An integer literal is an object integer in object code,
a meta value of a base type, or a numeral of a nat-like meta family such as `nat`; a literal at a type
that is not yet known waits until the end of its item and is an `int` if nothing determines its type
([Functions](meta/functions.md#literals-and-primitive-operations)). A numeral is a term of the two
constructors of its family, so it is an error ([E0901](errors/E0901.md)) if an integer literal checked
against a nat-like family is negative ([Inductive families](meta/families.md#numerals)).

The following program shows each kind of literal. Facts are printed with the escapes of string
literals, and negative numbers inside a fact in parentheses.

```hugin,run
reading : (sensor : string) -> (value : float) -> (samples : int) -> rel.
reading "north \"A\"" 2.5e1 3.
reading "south\tB" (-0.5) (-2).
```

```output
reading "north \"A\"" 25.0 3.
reading "south\tB" (-0.5) (-2).
```

## Punctuation

The remaining tokens are:

```text
:-   ?-   ->   =>   <:   <>   <=   >=   ..   ::   .   ,   ;   :   |   =   <   >
+    -    *    /    ^    (    )    {    }    [    ]    $    ⇑    '    ≡    ==   ⊢    |-
```

A prime `'` is a token only at the start of a token and directly before `(`: `'(` opens a
[quote](reflection.md#quotes), and its `(` is closed by a `)` like any parenthesis. Elsewhere a prime is
a character of a name (`x'`, `f''`).

A period `.` that directly follows a name, a variable or a closing parenthesis `)`, without space, and
is directly followed by a lowercase letter is a *selector*: `g.edge`, `E.loc`, `m.path`, `(tc g).path`
select a field or a column label. A period that directly follows a name, without space, and is directly
followed by a digit makes a *rule name* with the digits: `path.1`, `reached.2`
([Rule names](std/semantics.md#rule-names)). Every other `.` ends an item.

Parentheses `( )`, brackets `[ ]`, braces `{ }` and quotes `'( )` are pairs. It is an error
([E0005](errors/E0005.md)) if an item ends before an opening one is closed.

`⇑` (U+21D1) is the lift of [staging](meta/staging.md), and `^` where an operand starts is its ASCII
spelling: `^int` is `⇑int`. `$` starts a splice, or inside a quote a [hole](reflection.md#holes). A `<`
where an operand starts opens a [staging quote](meta/staging.md#explicit-quotes) `<t>`, which the next
`>` closes.

`≡` (U+2261) is the equality operator of the meta level, and `==` is its ASCII spelling: `n == m` is
`n ≡ m`. `=` itself is not an operator of the meta level: it defines (`x = e.`) and compares in object
formulas (see [Operators bound to meta functions](#operators-bound-to-meta-functions)).

`⊢` (U+22A2) is the turnstile of a [judgment](std/semantics.md#the-judgment-notation) `P ⊢ r t̄`, and
`|-` is its ASCII spelling.

A question mark `?` that is not followed by `-` is a [typed hole](meta/functions.md#typed-holes),
together with the name characters directly after it: `?`, `?rest`.

## Items

A file is a sequence of *items*. Every item ends with a period:

```text
File      ::= Item*
Item      ::= Declaration | Definition | Clause | SubtypeEdge
            | Rule | Query | Directive
```

The productions of the items are given in the chapters that define them:
[declarations](object/declarations.md), [subtyping edges](object/types.md#open-types),
[rules](object/rules.md), [queries](object/io.md#queries), [definitions and clauses](meta/clauses.md)
and [directives](directives.md). Several items may share a line. An item that starts with names
separated by commas, `a, b, c`, is a rule with several heads, or a
[declaration of several names](object/declarations.md#syntax) if a `:` follows the names.

An argument of an application or of a directive cannot start in column 0 of a line, nor can the operand
of `$`, `⇑`, `^`, `not` or a unary `-`, the content of a staging quote `<t>`, the body of a lambda `[x] e`, the formula of a query after `?-` or the body of a rule
after `:-`. So a missing period, or a missing formula, at the end of a line is reported where the next
item starts, and that item is still parsed. It is an error ([E0001](errors/E0001.md)) if an item does not
end with a period.

The following program declares a relation and gives it two facts on one line.

```hugin,run
city : type.  berlin : city.  paris : city.
road : city -> city -> rel.
road berlin paris.  road paris berlin.
```

```output
road berlin paris.
road paris berlin.
```

In the following program a stray `-` ends the first line. Its operand cannot be `e` in column 0, so the
error is reported there, and the declaration of `e` is parsed.

```hugin,compile_fail,E0001
-
e : int -> rel.
e 1.
```

## Syntax errors

A file with a syntax error ([E0001](errors/E0001.md) to [E0005](errors/E0005.md)) is rejected. The
compiler reports the syntax errors of the whole file: after an error, it resumes at the next item, at
the next `,` or `;` of a body, or at the next closing delimiter. An item with a syntax error is not
elaborated, and no error is reported for another item because it uses a name that the damaged item
declares. The following syntax errors leave no doubt about the intended text; an item with one of them
is elaborated as repaired:

- a missing period at the end of an item, before an item that starts in column 0 of a later line;
- `::` in place of the `:` of a declaration;
- `:=` in place of the `=` of a definition;
- a declaration head in parentheses, `(f) : τ.` ([E0004](errors/E0004.md));
- a rule name before a declaration, `@r f : τ.`;
- an empty `where` block.

The following program lacks the period after its first declaration. The error is reported where `path`
starts, and both declarations are elaborated.

```hugin,compile_fail,E0001
edge : int -> int -> rel
path : int -> int -> rel.
```

> **Note.** `hugin fix` applies the repairs to the file, and inserts a missing closing delimiter at the
> end of the item.

## Operators and precedence

Expressions of both levels share one grammar of operators. The binary operators, from the loosest to
the tightest binding:

| operators | associativity | meaning |
|---|---|---|
| `;` | left | disjunction of formulas |
| `,` | left | conjunction of formulas |
| `->` | right | function, relation and constructor types |
| `⊢` (`\|-`) | none | a [judgment](std/semantics.md#the-judgment-notation) `P ⊢[e] r t̄` (meta level) |
| `\|` | left | union of object types |
| `≡` (`==`) | none | equality (meta level) |
| `::` | right | a list with a first element (meta level) |
| `=` `<>` `<` `<=` `>` `>=` | none | comparisons |
| `+` `-` `^` | left | addition, subtraction, string concatenation |
| `*` `/` | left | multiplication, division |

Application by juxtaposition (`edge X Y`) binds tighter than every binary operator, and selection
`e.l` binds tighter than application. The prefix operators `not` and unary `-` apply to an application:
`not edge X Y` is `not (edge X Y)`. Comparison operators and `≡` do not associate: `A < B < C` is an
error ([E0001](errors/E0001.md)). `≡` binds looser than `::` and the arithmetic operators and tighter
than `->`, so `(n m : nat) -> n + m ≡ m + n` needs no parentheses. The right operand of `⊢` is an
optional database `[e]`, directly after the turnstile, and an atom, which is an application; `⊢` binds
tighter than `->`, so `tc G ⊢ path x y -> tc G ⊢ path y x` needs no parentheses. Among the levels of
user-defined operators, `⊢` is between 3 and 4, at the level of an operator of precedence 3.

On a nat-like meta type, `+` with an integer literal as its right operand is the successor applied that
many times, in expressions and in patterns: `N + 2` is `suc (suc N)`
([Inductive families](meta/families.md#numerals), [Clauses](meta/clauses.md#patterns)).

Three tokens are prefix where an operand starts and binary between operands: `-` is negation or
subtraction, `^` is the lift `⇑` or string concatenation, and `<` opens a staging quote or compares. So
`f -1` is a subtraction and `f ^A` a concatenation; an argument that starts with one of them is
parenthesised: `f (-1)`, `f (^A)`, `f (<t>)`. The content of `<t>` is parsed above the comparison level,
so a comparison in it is parenthesised: `<(X > 1)>`.

The meta level's `match` and `rewrite` are prefix forms like a lambda: the expression of the last branch
of a `match`, and the expression after the `in` of a `rewrite`, extend as far as the body of a lambda
does, and `|` ends a branch ([`match` and `rewrite`](meta/match.md#syntax)).

The head of a rule is parsed above the comparison level: in `p X, q X :- r X.` the comma separates two
heads. Inside a type, the comparison operators end the type, so that `x : int = 5.` parses.

### User-defined infix operators

```text
Infix     ::= "%infix" ("left" | "right" | "none") INT NAME "."
```

The directive `%infix assoc p op.` makes the name `op` a binary operator with associativity *assoc* and
precedence *p*. The operator binds tighter than the built-in operators of level *p* in the table below
and looser than those of level *p* + 1. `a op b` is the application `op a b`.

| level | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|
| operators | `;` | `,` | `->` | `\|` `≡` | comparisons | `+` `-` `^` | `*` `/` |

The operator is in effect in the whole file, also before the directive. A rule head is parsed above
the comparison level, so an operator of precedence 5 or more may appear in a head. Like an argument, the
operator does not continue an expression from column 0 of a line: there it starts the next item, such
as its declaration `op : …`.

The following program declares `likes` as an infix operator of precedence 5, which binds tighter than
the comparisons and looser than `+`. It uses the operator in facts, a head and a body.

```hugin,run
%infix none 5 likes.
person : type.  ann : person.  bob : person.  cy : person.
likes : person -> person -> rel.
ann likes bob.  bob likes ann.  cy likes ann.
mutual : person -> person -> rel.
mutual X Y :- X likes Y, Y likes X.
%output mutual.
```

```output
mutual ann bob.
mutual bob ann.
```

In the following program the period after `bob : person` is missing. The operator `likes` in column 0
starts the next item, its declaration: the error is reported there, and the declaration is parsed.

```hugin,compile_fail,E0001
%infix none 5 likes.
person : type.  ann : person.  bob : person
likes : person -> person -> rel.
ann likes bob.
```

### Operators bound to meta functions

```text
Binding   ::= "%infix" OP NAME "."
OP        ::= "+" | "-" | "*" | "/" | "^" | "≡" | "=="
```

The directive `%infix op f.` makes the symbol `op` denote the meta function `f` at the meta level: `a op
b` is the application `f a b`. The symbol keeps its place in the table above, so a binding never
changes how a file is parsed. `f` is a meta constant of the same file (a function, a definition, a
family or a constructor) that takes at least two explicit arguments; it is an error
([E0701](errors/E0701.md)) to bind another constant. Like an `%infix` operator, the binding is in effect
in the whole file, also before the directive. The standard library binds `+`, `-` and `*` to the
arithmetic of [`std/nat`](std/nat.md#operators), `+`, `-`, `*` and `/` to that of
[`std/int`](std/int.md#arithmetic), and `≡` to the equality `eq` of [`std/eq`](std/eq.md#equality).

A binding is in effect in every file in which the name of its function denotes that function: the
file that declares it, a file that opens it with `%use`, and every file if the prelude opens it. So
`%use "std/nat".` brings `+` on natural numbers, and `%use "std/nat" (minus).` only `-`. A
declaration of the file that shadows the name hides the binding.

Several bindings of one symbol may be in effect, such as `+` for `nat` and for `int`. Which one `a op b`
applies is decided by the types, without type classes:

1. The bindings whose result type has a head other than the expected type's are left out. The head of
   a type is its family or base type, or that it is a universe, a function type, a record type or
   object code `⇑A`. A type whose head is not known yet (an unknown, a type-level function application
   that does not compute yet) fits every binding.
2. If several bindings remain, or the expected type is not known, the left operand is inferred (the
   right one if the left one is a literal), and the bindings whose argument type there has another head
   are left out. A type variable of the context fits only a binding whose argument type is a variable
   of its own.
3. If one binding remains, `a op b` is its application. It is an error
   ([E0932](errors/E0932.md)) if several remain, and ([E0933](errors/E0933.md)) if none does, unless the
   operator has a built-in meaning for the type.

The arithmetic operators keep their built-in meanings, which apply where no binding fits: on a nat-like
type, `e + k` with an integer literal `k` is the successor, also where `+` is bound; on the meta `int`
the operators apply the functions of [`std/int`](std/int.md#arithmetic); on meta floats and strings
they are computed at compile time ([Functions](meta/functions.md#literals-and-primitive-operations)).
An integer literal next to an operand of unknown type makes it an `int`, as without bindings. Object
code never applies a binding, and `≡` there is an error ([E0933](errors/E0933.md)): object formulas
compare with `=`.

In a pattern, `p op q` is a constructor pattern if `op` denotes a constructor of the expected type, as
an infix constructor is in Agda and Haskell. It is an error ([E0915](errors/E0915.md)) if `op` denotes
only functions, since a pattern is built from constructors and variables; the successor `p + k` is a
pattern as before.

Each operand is elaborated once, so the time to resolve nested operators grows linearly with their
number. On an operator, the editor shows the function it denotes, and go to definition goes to it. A name
that `%use` items open for several meta constants is chosen between in the same way ([Overloaded opened
names](modules.md#overloaded-opened-names)).

The following program states and proves that `0` is a left unit of `+` on `nat`, and uses `-`, `*` and
the `+` of `int`.

```hugin,run
%use "std/eq".
%use "std/nat".
%use "std/int".
zeroPlus : (n : nat) -> 0 + n ≡ n.
zeroPlus 0 = refl.
zeroPlus (N + 1) = cong suc (zeroPlus N).
six : nat = 2 * 3.
shown : int -> rel.
shown (toInt (six - 1) + 10).
```

```output
shown 15.
```

In the following program both bindings of `+` fit, since the types of `x` and `y` are not known.

```hugin,compile_fail,E0932
%use "std/nat".
%use "std/int".
add = [x] [y] x + y.
```

> **Rationale.** The symbols of the meta level are overloaded as names are in Idris 2: by the types,
> without type classes, so that `std/nat` and `std/int` can both bind `+` without a class hierarchy.
> Idris elaborates each alternative and keeps those that succeed; comparing the heads of the types
> first, as Idris prunes its alternatives, and inferring each operand once keeps the resolution linear
> and free of backtracking. `=` stays the sign of definitions and object comparisons, as `≡` is
> Agda's identity type.
