# `std/reflect`

The module `std/reflect` declares what the compiler knows by name: lists, options and booleans, the
types of [reflection](../reflection.md), declarations as data, the primitive directives and the primitive
operations on symbols. The [prelude](../prelude.md) opens its lists, options, booleans, `same` and the
primitive directives; a program that writes directives or works with object syntax as data opens the
rest with `%use "std/reflect".`

## Lists, options and booleans

| declaration | meaning |
|---|---|
| `list A : data.` | lists of `A`, with the constructors `nil : list A` and `cons : A -> list A -> list A`, written `[]`, `[a, b]` and `x :: xs` |
| `append : list A -> list A -> list A` | the concatenation of meta lists |
| `option A : data.` | optional values, with `none : option A` and `some : A -> option A` |
| `bool : Type.` | meta booleans, with `true` and `false` |
| `if : bool -> A -> A -> A` | `if true x y` is `x`, `if false x y` is `y` |

`list` and `option` are [shared data types](../meta/families.md#shared-data): each is a meta inductive
family and an object family, with the derived functions `list.lift`, `list.reify`, `option.lift` and
`option.reify`. A list computed at compile time is a meta list, and it is used as an object list where
one is expected ([Staging](../meta/staging.md#lifting)). At the object level, like every constructor,
`nil` and `cons` build facts: a list is a fact once a rule head or an input file builds it. `bool` is a
meta type only: at the object level, truth is the presence of a fact. Both arguments of `if` are
evaluated.

The following program measures a meta list with `if`.

```hugin,run
nonzeros : list int -> int.
nonzeros [] = 0.
nonzeros (X :: Xs) = if (same X 0) 0 1 + nonzeros Xs.
nonzero : int -> rel.
nonzero (nonzeros [3, 0, 5]).
%output nonzero.
```

```output
nonzero 2.
```

## Reflection

The reflective types and their helpers are described in [Reflection](../reflection.md). Sequences of
syntax are meta lists (`list term`, `list formula`, `module = list item`).

| declaration | meaning |
|---|---|
| `sym` | references to object constants (`%builtin symbol`) |
| `index`, `izero`, `isuc` | de Bruijn indices of variables bound by aggregates |
| `arith_op` (`oadd`, `osub`, `omul`, `odiv`, `ocat`) | arithmetic operators |
| `cmp_op` (`ceq`, `cne`, `clt`, `cle`, `cgt`, `cge`) | comparison operators |
| `agg_op` (`acount`, `asum`, `amin`, `amax`) | aggregate operators |
| `term`, `formula`, `rule`, `item`, `module` | object syntax as data, written as quotes `'{ … }` ([Reflection](../reflection.md#quotes)) |
| `quoted A`, `qterm`, `raw` | a term of the object type `A`, made without a check, and its term ([Reflection](../reflection.md#typed-terms)) |
| `column`, `colof` | the column of an object constant at an index |
| `pick`, `openT`, `openTs`, `openF` | instantiate the variable bound at an index, as a higher-order hole does |

## Declarations and directives

| declaration | meaning |
|---|---|
| `measure` (`mvars`, `mlabels`) | the measures of `%terminates`: of variables or of labels |
| `attr` (`ainput`, `aoutput`, `aopen`, `aderivations`, `aterminates`) | the attributes that local directives attach |
| `decl` (`dconst`, `drule`, `derror`) | a declaration with its attributes, or an error |
| `attach : attr -> decl -> decl` | adds an attribute to a declaration |
| `input`, `output`, `open`, `derivations` | the primitive local directives, of type `decl -> decl` |
| `terminates : measure -> formula -> decl` | the directive `%terminates` |
| `modes` (`mnone`, `minput`, `moutput`) | modes indexed by the labels of a relation's columns |

## Primitives

| declaration | meaning |
|---|---|
| `same : A -> A -> bool` | equality of symbols and literals |
| `labels : sym -> list string` | the labels of a constant's columns |
| `derive : sym -> string -> sym` | the derived constant `r.l` |
| `derived : sym -> bool` | whether a constant is derived |

A primitive is declared `x : A = %builtin p.`; it is an error ([E0103](../errors/E0103.md)) if `A` is not
the type of the primitive `p`.
