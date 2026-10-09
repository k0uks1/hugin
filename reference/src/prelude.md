# The prelude

The *prelude* is a Hugin file bundled with the compiler, `<stdlib>/prelude.hgn`. It is included in every
program unless the option `--no-prelude` is given. Its scope encloses every file of a compilation, so its
names are in scope everywhere without an import, and a program may shadow any of them
([Modules](modules.md#scopes)). This chapter lists what it provides.

The prelude is ordinary Hugin source. Its families and functors create object constants only where a
program uses them.

## Base types

`int`, `float` and `string` are built into the compiler. Their names are in scope in every program that
includes the prelude ([Object types](object/types.md#base-types)).

## Lists, options and pairs

| declaration | meaning |
|---|---|
| `list A : data.` | lists of `A`, with the constructors `nil : list A` and `cons : A -> list A -> list A`, written `[]`, `[a, b]` and `x :: xs` |
| `len : (l : list A) -> (n : int) -> rel.` | the length of every list that is a fact |
| `append : list A -> list A -> list A` | the concatenation of meta lists |
| `option A : data.` | optional values, with `none : option A` and `some : A -> option A` |
| `pair A B : type = { fst : A, snd : B }.` | a struct of two values |

`list` and `option` are [shared data types](meta/families.md#shared-data): each is a meta inductive
family and an object family, with the derived functions `list.lift`, `list.reify`, `option.lift` and
`option.reify`. A list computed at compile time is a meta list, and it is used as an object list where
one is expected ([Staging](meta/staging.md#lifting)). `pair` is an object struct only; meta code uses
record types. `bool` is a meta type only: at the object level, truth is the presence of a fact.

At the object level, like every constructor, `nil` and `cons` build facts: a list is a fact once a rule
head or an input file builds it. `len` is defined by guarded induction on the list:

```hugin,ignore
len nil 0.
len (cons X L) M :- cons X L, len L N, M = N + 1.
```

So `len` measures the lists that are facts. A program that asks for the length of lists it builds in
rule bodies writes `%demand len +l -n.`; the demand rules then build the lists
([Directives](directives.md#demand)).

The following program measures a list given as a fact.

```hugin,run
words : list string -> rel.
words ["a", "b"].
?- words L, len L N.
```

```output
?- words L, len L N.
L = cons "a" (cons "b" nil), N = 2.
```

## Graphs

| declaration | meaning |
|---|---|
| `graph : Type = { node : type, edge : node -> node -> rel }.` | the signature of graphs |
| `tc (g : graph)` | a functor: its relation `path` is the transitive closure of `g.edge` |
| `bounded (g : graph) (limit : int)` | a functor: its relation `hop X Y N` holds if there is a walk of `N` edges from `X` to `Y`, for `N ≤ limit` |

The following program applies both functors to a graph of three cities.

```hugin,run
city : type. berlin : city. paris : city. rome : city.
road : city -> city -> rel.
road berlin paris. road paris rome.
roads = tc { node = city, edge = road }.
short = bounded { node = city, edge = road } 2.
%output roads.path. %output short.hop.
```

```output
roads.path berlin paris.
roads.path berlin rome.
roads.path paris rome.
short.hop berlin paris 1.
short.hop berlin rome 2.
short.hop paris rome 1.
```

## Reflection

The reflective types and their helpers are described in [Reflection](reflection.md). `quoted A` is
the typed layer over `term`; the other types are the representation and carry no object types.
Sequences of syntax are meta lists (`list term`, `list formula`, `module = list item`).

| declaration | meaning |
|---|---|
| `sym` | references to object constants (`%builtin symbol`) |
| `index`, `izero`, `isuc` | de Bruijn indices of variables bound by aggregates |
| `arith_op` (`oadd`, `osub`, `omul`, `odiv`, `ocat`) | arithmetic operators |
| `cmp_op` (`ceq`, `cne`, `clt`, `cle`, `cgt`, `cge`) | comparison operators |
| `agg_op` (`acount`, `asum`, `amin`, `amax`) | aggregate operators |
| `quoted : ⇑type -> Type`, `qterm : term -> quoted A`, `raw : quoted A -> term` | quoted terms: a term of the object type `A`, the constructor that makes one from a `term` without a check, and the term of one ([Reflection](reflection.md#typed-terms)) |
| `term`, `formula`, `rule`, `item`, `module` | object syntax as data, without object types, written as quotes `'{ … }` ([Reflection](reflection.md#quotes)) |
| `qatom : quoted A -> formula` | a term of a type of facts as an atom (primitive, [Reflection](reflection.md#typed-atoms)) |
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
| `demand : (r : sym) -> modes (labels r) -> module -> module` | the directive `%demand` |

The helper functions of `demand` have names that start with `d` (`dmodule`, `dprefix`, …), with the set
operations `member`, `sdiff` and `shares` on lists of strings, the test `msym` on lists of symbols and
the binding analysis `tvarsOf`, `tsvars`, `fvars`, `fbound`, `fneeds`, `plain` and `plains`. They are
ordinary definitions, which programs may use, but they are not part of the documented interface of the
prelude.

## Booleans and primitives

| declaration | meaning |
|---|---|
| `bool` (`true`, `false`) | meta booleans |
| `band`, `bor` | conjunction and disjunction of meta booleans |
| `same : A -> A -> bool` | equality of symbols and literals (primitive) |
| `labels : sym -> list string` | the labels of a constant's columns (primitive) |
| `derive : sym -> string -> sym` | the derived constant `r.l` (primitive) |
| `derived : sym -> bool` | whether a constant is derived (primitive) |
| `qatom : quoted A -> formula` | a typed atom as a formula (primitive) |

A primitive is declared `x : A = %builtin p.`; it is an error ([E0103](errors/E0103.md)) if `A` is not
the type of the primitive `p`.
