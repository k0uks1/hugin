# Directives

A *directive* `%d a₁ … aₙ.` applies the meta function `d` to its arguments, and the type of the
application says what it changes in the program: one declaration, the items at its place, or all rules
and queries of the file. The directives of the standard library, such as `%input`, `%output` and
`%demand`, are ordinary meta functions, and a program can define its own. This chapter defines the syntax
and resolution of directives, their footprints, the order of expansion, the directives of the standard
library and `%demand` in detail.

## Syntax

```text
Directive  ::= DIRECTIVE DirArg* "."                   (standalone)
             | DIRECTIVE DirArg* Declaration           (prefix form)
             | "%infix" ("left" | "right" | "none") INT NAME "."
DirArg     ::= Atom-like expression | ModeItem+
ModeItem   ::= ("+" | "-") NAME?
```

The arguments of a directive are atoms of the expression grammar: names, paths `m.r`, variables,
literals, rule names `@r` and parenthesised expressions. A run of *mode items* such as `+e +g -t` is one
argument ([`%demand`](#demand)).

In the *prefix form*, a directive without a period is followed by a declaration, which is recognised by
its `:`. The directive applies to that declaration: `%output path : node -> node -> rel.` declares `path`
and makes it an output relation.

`%infix` has a syntax of its own and is handled by the parser ([Lexical
structure](lexical-structure.md#user-defined-infix-operators)). `%builtin` and `%import` are expressions,
not directives ([Object types](object/types.md#base-types), [Modules](modules.md#imports)). `%use` and
`%export` are items of a file's scope, not directives ([Modules](modules.md#opening-modules)).
`%complete` is a requirement in a signature ([Modules](modules.md#signatures)); it is an error
([E0004](errors/E0004.md)) elsewhere. The directive `%partial` of earlier versions has been removed; it
is an error ([E0001](errors/E0001.md)).

## Resolution and arguments

`%d` resolves the name `d` like any name: in the file, the names it opens with `%use`, and the prelude.
So `%use` makes the directives of a module available: after `%use "lib/closures".`, a function
`symmetric` of that file is the directive `%symmetric`. It is an error ([E0101](errors/E0101.md)) if no
`d` is in scope; the diagnostic suggests a directive with a similar name. It is an error
([E0109](errors/E0109.md)) if two `%use` items open `d` for different functions. The compiler elaborates
the application `d a₁ … aₙ` with the arguments checked against `d`'s parameter types, with stage
inference. The arguments of a directive are object syntax, like the item they stand in: an argument at a
parameter of a reflective type (`term`, `formula`, `rule`, `item`, `sym`, `decl`, `measure`) or of type
`quoted A` is quoted implicitly, as if it were written in a [quote](reflection.md#quotes) `'( … )`. The
quote may also be written explicitly. In particular:

- where a `decl` is expected, the name of an object constant (also a path, a family, or a member of a
  module body) is its declaration `dconst ⟨r⟩ []`, and a rule name `@r` is `drule "r" []`;
- where a `sym` is expected, the name of an object constant is its symbol;
- where a `measure` is expected, the measure syntax of `%terminates` is quoted;
- a meta value is passed in a hole, `%d $x.`; at a `decl` or `sym` parameter, an argument that is not a
  name (or a hole) is elaborated as meta code;
- an argument at a parameter of type `quoted A` is a term of type `A` (`%d 3.` for `quoted int`), typed
  as the quote `'( 3 )` checked against `quoted A`;
- a run of mode items is elaborated to the `modes` data of `std/reflect`.

An argument of the wrong type is an error ([E0901](errors/E0901.md)).

## Footprints

The *footprint* of a directive is the part of the program it changes. It is determined by the type of the
application `d a₁ … aₙ`, with implicit arguments inserted.

| type of the application | footprint | effect |
|---|---|---|
| `decl` | local | attaches attributes to the declaration that the application describes |
| `decl -> decl` (prefix form only) | local | the same, for the declaration that follows the directive |
| `list item`, `item`, `rule`, `list rule` | additive | adds the items at the place of the directive |
| `module -> module` | module-wide | rewrites the rules and queries of the file |

It is an error ([E1001](errors/E1001.md)) if the application has another type. In the prefix form, it is
an error ([E1002](errors/E1002.md)) if the application does not have type `decl -> decl`, and
([E1003](errors/E1003.md)) if its result describes another declaration than the one it is attached to.

A directive rejects its arguments by returning `derror "message"` (for `decl`) or an item
`ierror "message"`. The message is reported at the directive ([E1000](errors/E1000.md)).

### Local directives

A `decl` is an object constant or a rule name with a list of *attributes*: `dconst s as` or `drule n as`.
The attributes are what the compiler implements: `ainput`, `aoutput`, `aopen`, `aderivations` and
`aterminates`. A local directive receives the declaration without the attributes of other directives, so
it can only add attributes; the attributes of all local directives on a declaration accumulate. A local
directive in a module body refers to the body's constants, and applies to each instance of the body; on a
family, it applies to each instance of the family. The declaration's type is not data: a local directive
cannot change a type.

It is an error ([E0701](errors/E0701.md)) if an attribute does not fit its declaration, for example
`%input` on a rule name, or a measure that names a label the relation does not have.

### Additive directives

An additive directive is [reflected](reflection.md#reflecting-data-into-the-program) like an item `$e.`
at its place. Its items carry the note "in expansion of `%d …`" in diagnostics.

### Module-wide directives

The *module* of a file is the list of its rules (named rules as `inamed`), queries and reflected items,
as data. If a file has module-wide directives, its rules and queries are those of the expansion:

1. The module starts as the rules, queries and `$e.` items of the file, in source order.
2. The additive and module-wide directives are expanded in source order. An additive directive inserts
   its items at its place. A module-wide directive replaces the whole module with its result, so it sees
   every rule and query of the file and the items of the directives before it, but not the items of
   additive directives after it.
3. The result is reflected and elaborated like hand-written code. An item that a directive passes on
   unchanged keeps its place and its position in diagnostics; a new item is placed at the directive.

Additive and module-wide directives are allowed at the top level of a file only; in a module body they
are an error ([E0907](errors/E0907.md)).

The following program has a module-wide directive `%mirror` that adds the reverse of every rule
deriving `edge`. It sees the edge added by `%loop c` before it, but not the one added by `%loop a` after
it.

```hugin,run
%use "std/reflect".
node : type.
a, b, c, d : node.
edge : node -> node -> rel.
edge a b.
mirror : module -> module.
mirror [] = [].
mirror ('( edge $X $Y :- $..B ) :: Rest) = '( edge $X $Y :- $..B ) :: '( edge $Y $X :- $..B ) :: mirror Rest.
mirror (I :: Rest) = I :: mirror Rest.
loop : term -> list item.
loop N = '( edge $N d. ).
%loop c.
%mirror.
%loop a.
%output edge.
```

```output
edge a b.
edge a d.
edge b a.
edge c d.
edge d c.
```

## The primitive directives

The module [`std/reflect`](std/reflect.md#declarations-and-directives) defines the directives whose
attributes the compiler implements, and the prelude opens them.

| directive | type | meaning |
|---|---|---|
| `%input r.` | `decl -> decl` | `r` is a complete input relation ([Input facts](object/io.md#input-facts)) |
| `%open r.` | `decl -> decl` | `r` is an incomplete input relation ([Completeness](object/negation.md#completeness)) |
| `%output r.` | `decl -> decl` | `r` is an output relation ([Output relations](object/io.md#output-relations)) |
| `%derivations r.`, `%derivations @n.` | `decl -> decl` | derivation facts ([Derivation facts](object/io.md#derivation-facts)) |
| `%terminates m p.` | `measure -> formula -> decl` | a termination measure ([Termination](object/termination.md#declared-measures)) |
| `%demand r m.` | `(r : sym) -> modes (labels r) -> module -> module` | demand-driven evaluation of `r` (below) |

`%input r.` is the application `input '( r )`, with `r` quoted implicitly as a `decl`. The functions
`input`, `output`, `open` and `derivations` have the type `decl -> decl`, so they can also be used in the
prefix form, and they compose like functions.

The following program defines a local directive `%io` from two primitive ones and uses it, and
`%output`, in the prefix form.

```hugin,run
%use "std/reflect".
node : type. a, b : node.
io : decl -> decl.
io D = input (output D).
%io marked : node -> rel.
%output seen : node -> rel.
seen X :- marked X.
```

```facts
marked a.
```

```output
marked a.
seen a.
```

## User-defined directives

A directive is any meta function whose application has a directive type. The following program defines
`%symmetric`, which takes a relation as object code and adds the rule that makes it symmetric.

```hugin,run
%use "std/reflect".
person : type. ann, bob, cid : person.
symmetric : (r : ⇑(A -> A -> rel)) -> list item.
symmetric R = '( R Y X :- R X Y. ).
friend : person -> person -> rel.
%symmetric friend.
friend ann bob.
friend bob cid.
%output friend.
```

```output
friend ann bob.
friend bob ann.
friend bob cid.
friend cid bob.
```

[`std/directives`](std/directives.md) defines what directive authors need beyond `std/reflect`: the parts
of rules and modules, the calls of a relation, the binding analysis of terms and formulas, fresh variable
names and `reject`.

## Demand

`%demand r m.` makes the relation `r` *demand-driven*: `r` is computed only for the inputs that some rule
or query asks for. The directive is the module-wide meta function `demand` of
[`std/demand`](std/demand.md), written in Hugin with quoted patterns. It implements the magic-sets
transformation as ordinary rules, which are typed, stratified and checked for termination like
hand-written rules.

### Modes

The mode argument `m` is a run of mode items, one per column of `r`: `+` for an *input* column, `-` for
an *output* column. An item may name the column's label: `%demand typed +e +g -t.` The modes are typed
by the labels of `r`'s columns (`modes (labels r)`), so it is an error ([E0901](errors/E0901.md)) if an
item names another label than the column's, or if the number of items differs from the number of
columns. An item without a label matches any column.

### What `%demand` generates

For the relation `r` with input columns `ī`, `%demand r m` changes the module as follows.

1. It declares the *demand relation* `r.check`, a [derived
   constant](reflection.md#symbols-and-derived-constants) whose columns are the input columns of `r`.
2. Every rule of `r` gets the *guard* `r.check ī` before its body: `r t̄ :- r.check t̄ᵢ, body`. A
   wildcard in an input column of the head is named, so that the guard binds it. The names are
   `_a#0`, `_ba#0`, …, which no variable of the program can capture
   ([Reflection](reflection.md#reflecting-data-into-the-program)); they are shown as `_a`, `_ba`, …
3. Every call `r t̄` in every rule and query of the module (positive, negated, in an aggregate or in a
   disjunction) gets a *demand rule* `r.check t̄ᵢ :- prefix`, where `prefix` is the conjunction of the
   formulas before the call, the guard first in a rule of `r`. A demand rule in a rule of `r` is a
   *propagation rule*; one outside `r` is a *seed rule*. A call inside an aggregate uses the formulas
   before the aggregate.

The prefix of a demand rule is *pruned*: demand rules are positive, and they do not wait for answers they
do not need. A negation is left out. A call of a demand-driven relation, or an aggregate, is kept only if
it binds a variable that the call's inputs or the kept formulas need and that the other formulas do not
bind. A smaller prefix only adds demand, never answers.

The demand rules are ordinary rules. A demand rule that builds a term as an input makes the term a fact
([Facts and identity](object/facts.md)): the contexts of a type checker become facts of their
constructor.

The following program computes Fibonacci numbers on demand. Without `%demand`, the rule would need a
bound on `N` to terminate; with it, `fib` is computed for the numbers that the query asks for and the
numbers below them.

```hugin,run
fib : (n : int) -> (f : int) -> rel.
%demand fib +n -f.
fib 0 0.
fib 1 1.
fib N F :- N > 1, A = N - 1, B = N - 2, fib A FA, fib B FB, F = FA + FB.
?- fib 30 F.
```

```output
?- fib 30 F.
F = 832040.
```

The option `--print-after stage` shows the generated rules. For this program they are:

```text
fib.check : (n : int) -> rel.
fib 0 0 :- fib.check 0.
fib 1 1 :- fib.check 1.
fib N F :- fib.check N, N > 1, A = N - 1, B = N - 2, fib A FA, fib B FB, F = FA + FB.
fib.check A :- fib.check N, N > 1, A = N - 1, B = N - 2.
fib.check B :- fib.check N, N > 1, A = N - 1, B = N - 2.
fib.check 30.
```

The propagation rules leave out the calls `fib A FA` and `fib B FB`, whose answers they do not need. So
`fib.check` is in a component of its own and terminates by descent (A); `fib` terminates by guarded
induction or descent, guarded by `fib.check` ([Termination](object/termination.md)).

The following program has a variable `_a` in the body of a rule whose head has a wildcard in the input
column. The guard binds the wildcard as `_a#0`, which is not the program's `_a`, so the rule derives
`reach b a` for the demanded input `b`.

```hugin,run
node : type. a, b, c : node.
edge : node -> node -> rel.
start : node -> rel.
reach : (from : node) -> (to : node) -> rel.
%demand reach +from -to.
edge a b. edge c a. start c.
reach _ Y :- start _a, edge _a Y.
?- reach b Y.
```

```output
?- reach b Y.
Y = a.
```

### Several demand-driven relations

Several `%demand` directives are expanded in source order, each seeing the rules generated by the ones
before it. The rules generated from a rule follow it, and a later `%demand` that guards a rule also
guards the demand rules that follow it. So the order of the `%demand` directives does not change the
program.

The following type checker makes `lookup` and `typed` demand-driven. The demand rules of `typed` build
the contexts `bind G X T1` as facts.

```hugin,run
name : type = string.
expr : type. ref : name -> expr. lam : name -> typ -> expr -> expr. app : expr -> expr -> expr.
typ : type. base : string -> typ. arrow : typ -> typ -> typ.
ctx : type. empty : ctx. bind : ctx -> name -> typ -> ctx.
lookup : (g : ctx) -> (x : name) -> (t : typ) -> rel.
%demand lookup +g +x -t.
lookup (bind _ X T) X T.
lookup (bind G Y _) X T :- lookup G X T, X <> Y.
typed : (e : expr) -> (g : ctx) -> (t : typ) -> rel.
%demand typed +e +g -t.
typed (ref X) G T :- lookup G X T.
typed (lam X T1 B) G (arrow T1 T2) :- typed B (bind G X T1) T2.
typed (app F A) G T1 :- typed F G (arrow T0 T1), typed A G T0.
program : expr -> rel.
program (lam "x" (base "int") (ref "x")).
program (app (lam "x" (base "int") (ref "x")) (ref "y")).
?- program E, typed E empty T.
```

```output
?- program E, typed E empty T.
E = lam "x" (base "int") (ref "x"), T = arrow (base "int") (base "int").
```

> **Limitation.** A demand that needs an answer of the relation it demands, as in Ackermann's function,
> puts the demand relation and the relation into one component, which the termination check rejects
> ([Termination](object/termination.md#limitation)).

> **Note.** `%demand` cannot be applied to a relation of a library from the library itself on behalf of
> its callers, since a module-wide directive rewrites its own file only. A program that calls `len` of
> [`std/list`](std/list.md) on lists it builds writes `%demand len +l -n.` itself; the demand rules of
> the program build the lists, and the library's relation measures them.
