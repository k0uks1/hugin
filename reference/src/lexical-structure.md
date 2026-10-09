# Lexical structure

A Hugin source file is a sequence of Unicode characters in UTF-8. The lexer divides it into *tokens*,
which the parser groups into items. This chapter defines the tokens, the comments, the items and the
precedence of operators. Facts files (see [Input facts](object/io.md#input-facts)) use the same tokens.

## Whitespace and comments

Spaces, tabs and line breaks separate tokens and have no other meaning, with one exception: an
argument, and the formula after `?-` or `:-`, cannot start in column 0 of a line (see [Items](#items)).

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
```

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

An *integer literal* denotes a 64-bit signed integer. It is an error ([E0003](errors/E0003.md)) if its
value is larger than 2⁶³ − 1; the literal `9223372036854775808` is only valid after a unary minus.

A *float literal* denotes a 64-bit IEEE 754 number. It has digits on both sides of the point: `1.0`,
`2.5e-3`. The text `1.` is the integer `1` followed by a period.

A *string literal* is enclosed in double quotes and cannot span lines. Its escapes stand for a double
quote, a backslash, a line feed, a tab and the Unicode code point with the given hexadecimal number. It
is an error ([E0003](errors/E0003.md)) to use another escape or a code point that is not a Unicode
scalar value, and ([E0002](errors/E0002.md)) to leave a string unterminated.

There is no literal for negative numbers. `-5` is the unary minus applied to `5`; the parser folds it
into the literal −5.

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
:-   ?-   ->   <:   <>   <=   >=   ..   ::   .   ,   ;   :   |   =   <   >
+    -    *    /    ^    (    )    {    }    [    ]    $    ⇑    '
```

A prime `'` is a token only at the start of a token and directly before `{`: `'{` opens a
[quote](reflection.md#quotes), and its `{` is closed by a `}` like any brace. Elsewhere a prime is a
character of a name (`x'`, `f''`).

A period `.` that directly follows a name, a variable or a closing parenthesis `)`, without space, and
is directly followed by a lowercase letter is a *selector*: `g.edge`, `E.loc`, `m.path`, `(tc g).path`
select a field or a column label. Every other `.` ends an item.

Parentheses `( )`, brackets `[ ]`, braces `{ }` and quotes `'{ }` are pairs. It is an error
([E0005](errors/E0005.md)) if an item ends before an opening one is closed.

`⇑` (U+21D1) is the lift of [staging](meta/staging.md); `$` starts a splice, or inside a quote a
[hole](reflection.md#holes).

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
and [directives](directives.md). Several items may share a line.

An argument of an application or of a directive cannot start in column 0 of a line, nor can the operand
of `$` or `⇑`, the formula of a query after `?-` or the body of a rule after `:-`. So a missing period,
or a missing formula, at the end of a line is reported where the next item starts, and that item is
still parsed. It is an error ([E0001](errors/E0001.md)) if an item does not end with a period.

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
| `\|` | left | union of object types |
| `::` | right | a list with a first element (meta level) |
| `=` `<>` `<` `<=` `>` `>=` | none | comparisons |
| `+` `-` `^` | left | addition, subtraction, string concatenation |
| `*` `/` | left | multiplication, division |

Application by juxtaposition (`edge X Y`) binds tighter than every binary operator, and selection
`e.l` binds tighter than application. The prefix operators `not` and unary `-` apply to an application:
`not edge X Y` is `not (edge X Y)`. Comparison operators do not associate: `A < B < C` is an error
([E0001](errors/E0001.md)).

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
| operators | `;` | `,` | `->` | `\|` | comparisons | `+` `-` `^` | `*` `/` |

The operator is in effect in the whole file, also before the directive. A rule head is parsed above
the comparison level, so an operator of precedence 5 or more may appear in a head.

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
