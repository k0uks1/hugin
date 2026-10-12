# Modules, functors and libraries

A *module* is a record whose fields are the constants declared in a *module body* or in a file. Modules
group object constants and meta definitions; *functors* are meta functions that return modules; and every
source file is a module that other files can import. This chapter defines module bodies and their
instances, functors, signatures and ascription, imports and the scope of libraries.

## Module bodies

```text
ModuleBody ::= "{" Item* "}"
```

A *module body* is a sequence of items in braces: declarations, definitions, clauses, rules, queries and
local directives. Its value is a module: a record with a field for every constant it declares. A member
is selected with a path `m.r`; paths nest (`lib.reach`).

The items of a body are elaborated in a scope of their own, inside the scope of the enclosing file. They
see the body's members, the parameters of an enclosing functor and the names of the file. A member is in
scope in the whole body, also before its declaration ([Scopes](#scopes)).

A body accepts what a file accepts for meta functions. A declaration `f : A.` with a meta type and the
clauses `f p̄ = e.` of the same body define a *member function*, a field of the module. Its clauses are
those of the body that declares it ([Clauses](meta/clauses.md)); member functions may refer to later
members and to each other. A member function is checked for [coverage](meta/coverage.md) and
[termination](meta/termination.md) where it is written, and diagnostics name it by its path
(`lib.double`, `tc.step` for a functor `tc`).

Likewise, a declaration `f : τ₁ -> … -> τₙ -> prop.` without a definition and the rules `f t̄ :- φ.` of
the same body define a [formula function](meta/staging.md#formula-functions) of the body, a field of the
module. Its clauses are the rules of the body that declares it, and they may use the body's members,
also later ones. A formula function of a body that refers to itself, directly or through other members,
is an error ([E0105](errors/E0105.md)), as in a file, and so is one without clauses a warning
([W0005](errors/W0005.md)); diagnostics name it by its path.

A member function or formula function is elaborated once, where the body is written, and not for each
instance. It is a function of the parameters of the enclosing functors and of the object constants of the enclosing bodies:
the field of an instance is that function for the instance's arguments and object constants. Two
instances of a functor have fields that compute the same results, and object code that a field returns
mentions the object constants of its own instance.

The members of a body are elaborated in dependency order, as a file's items are ([Order of
elaboration](meta/index.md#order-of-elaboration)), with one difference: the object constants come first,
with the definitions their types mention, so that every member function is a function of the same object
constants. Then the other members, the clauses of the member functions and the rules of the formula
functions are elaborated by the cycles of their dependency graph, each cycle after the members it refers
to; inside a cycle, the signatures and definitions come first, then the clauses and rules, each function
one item, and no function of the cycle computes in it. At the end of each cycle, termination and the
cycles of its formula functions are checked. The object items come last. A member's type or value may
therefore compute with a member function written anywhere in the body:

```hugin
nat : Type. zero : nat. suc : nat -> nat.
vec : Type -> nat -> Type.
vnil : vec A zero.
vcons : A -> vec A N -> vec A (suc N).
lib = {
  vec3 : Type = vec int (plus one (suc one)).
  v : vec3 = vcons 1 (vcons 2 (vcons 3 vnil)).
  one : nat = suc zero.
  plus : nat -> nat -> nat.
  plus zero N = N.
  plus (suc M) N = suc (plus M N).
}.
```

Inside a body, `here` is the body's own program: `programOf here` is the program of its rules
([`std/quote`](std/quote.md#programs-as-values)), at the parameters of the enclosing functor, and `here ⊢
r t̄` a judgment about it. The members that use it, directly or through other members (with the clauses
of a member function and the rules of a formula function), are *program-dependent*: they are elaborated
after the body's object items, as a file's program-dependent declarations are ([Declarations about the
file's program](meta/index.md#declarations-about-the-files-program)), and they are fields of the module
like the other members, so every instance has them. Its object items and its object constants cannot use
them ([E0962](errors/E0962.md)).

```hugin
%use "std/semantics".
graph2 : Type = { node : type, edge : node -> node -> rel }.
walks (g : graph2) = {
  walk : g.node -> g.node -> rel.
  walk X Y :- g.edge X Y.
  walk X Z :- walk X Y, walk Y Z.
  walkTrans : {D : db} -> {x y z : ⇑g.node} -> here ⊢[D] walk x y -> here ⊢[D] walk y z -> here ⊢[D] walk x z.
  walkTrans P Q = walk.2 P Q.
}.
city : type. berlin, paris : city.
road : city -> city -> rel.
fast = walks { node = city, edge = road }.
```

Here `fast.walkTrans` is the lemma for the instance's program, `walks { node = city, edge = road } ⊢ …`.

In these members, a relation of the body, and a relation of a variable of its context such as the
functor's parameter (`g.edge`), is written unqualified as a proposition of the body's program: `walk x y`
for `here ⊢ walk x y`, and `⊢ r t̄` for a nullary relation or a named database
([Relations as propositions](std/semantics.md#inside-bodies-and-files)). A member that writes one is
program-dependent, as one that writes `here`. So `walkTrans` above may be stated `{x y z : g.node} -> walk
x y -> walk y z -> walk x z`.

`%opaque m₁ … mₙ.` in a body makes its member definitions and member functions `mᵢ` opaque, as at the top
level ([Opaque definitions](meta/index.md#opaque-definitions)); it is an error
([E0701](errors/E0701.md)) if `mᵢ` is not a meta member of the body.

Two programs that a file accepts are rejected in a body. A typed definition and a signature that need
each other (`x : nat = pick zero.` with `pick : nat -> sel x.`) are an error, since a member's value
cannot follow its type there. And a formula function or member function is checked for cycles with the
whole value of each member it uses, not only with the member a path selects: in a body that applies a
functor `mk` of the body to make a member `inst`, a formula function `h` that uses `inst.a` refers to
itself ([E0105](errors/E0105.md)) if any member of `mk`'s body uses `h`, although at the top level the
same program is accepted ([Formula functions](meta/staging.md#formula-functions)).

It is an error ([E0907](errors/E0907.md)) to use in a module body: refinements, families of object
constants, meta inductive families, meta declarations without a definition or clauses, postulates,
reflected items `$e.`, `%use`, and additive or module-wide directives. A member that is rejected is left out, and its uses in the body are not reported again. It is
an error ([E0915](errors/E0915.md)) to write clauses in a body for a function that the body does not
declare, and ([E0105](errors/E0105.md)) if a definition of a body refers to itself. It is an error
([E0107](errors/E0107.md)) to select a member of a value that is not a module.

The following functor defines two mutually recursive member functions, `even` and `odd`, and a rule
that calls the member function `weight`. `parity` refers to `even` before its declaration. The two
instances share the functions, each with its own relation `cost`.

```hugin,run
graph : Type = { node : type, edge : node -> node -> rel }.
stepping (g : graph) = {
  parity : nat -> string.
  parity N = label (even N).
  even : nat -> bool.
  even 0 = true.
  even (N + 1) = odd N.
  odd : nat -> bool.
  odd 0 = false.
  odd (N + 1) = even N.
  label : bool -> string.
  label true = "even".
  label false = "odd".
  weight : nat -> int.
  weight 0 = 0.
  weight (N + 1) = 10 + weight N.
  cost : g.node -> g.node -> int -> rel.
  cost X Y (weight 2) :- g.edge X Y.
}.
city : type. berlin, paris : city.
road : city -> city -> rel.
road berlin paris.
s1 = stepping { node = city, edge = road }.
s2 = stepping { node = city, edge = road }.
answer : string -> rel.
answer (s1.parity 3).
%output answer. %output s1.cost. %output s2.cost.
```

```output
answer "odd".
s1.cost berlin paris 20.
s2.cost berlin paris 20.
```

## Instances

A module body is *generative*: evaluating it creates fresh object constants for the object constants it
declares, and stages its rules and queries with them. A definition `m = { … }.` or `m = f a.` is
evaluated once, so all uses of `m` share one *instance*. Two definitions that evaluate the same body,
also by applying a functor to the same arguments, create two instances with distinct relations.

The object constants of an instance are named by the path through which a program reaches it:

- the instance that is the value of a definition `m = …` is named `m`: the relation `path` of
  `r1 = tc g` is `r1.path`;
- an instance that a member `x = …` of a body defines is named after the body's instance and the member:
  in `weak = rtc g`, the member `v = vertices g` of `rtc`'s body is the instance `weak.v`, with the
  relation `weak.v.vertex`;
- an instance that is an argument of an application has no path and is anonymous: in
  `back = tc (reverse g)`, the instance of `reverse g` is `_m1`, and `back` is the instance of `tc`.

Anonymous instances, and instances that no definition names, are called `_m1`, `_m2`, …; a name that
repeats gets a suffix `#k`. The relation that a program names by a path, such as `weak.v.vertex`, is
printed under that path.

The following program composes two functors of [`std/graph`](std/graph.md). `back` is the instance of
`tc`, `s.r` the member `r = rtc g` of `scc`'s body, and the reversed graph passed to `tc` is anonymous.

```hugin,run
%use "std/graph".
city : type. a, b, c : city.
road : city -> city -> rel.
road a b. road b c. road c b.
back = tc (reverse { node = city, edge = road }).
s = scc { node = city, edge = road }.
%output back.path. %output s.r.path.
```

```output
back.path b a.
back.path b b.
back.path b c.
back.path c a.
back.path c b.
back.path c c.
s.r.path a a.
s.r.path a b.
s.r.path a c.
s.r.path b b.
s.r.path b c.
s.r.path c b.
s.r.path c c.
```

## Functors

A *functor* is a meta function that returns a module, written as a definition with parameters whose
right-hand side is a module body: `tc (g : graph) = { … }.` Its parameters are typed by
[signatures](#signatures). An application `tc { node = city, edge = road }` evaluates the body with the
parameter bound to the argument, and creates an instance.

The object code of a functor's body is [typed](object/types.md#functor-bodies) once, where the body is
written. The object types that a parameter gives are abstract in the body; checks that depend on what
such a type is are made for each instance. The subtyping edges of a module body are in scope for all of
its rules.

The following program applies the functor `tc` (transitive closure) of [`std/graph`](std/graph.md) twice
to the same graph. The two applications create two distinct relations `r1.path` and `r2.path`.

```hugin,run
%use "std/graph".
city : type. berlin, paris, rome : city.
road : city -> city -> rel.
road berlin paris. road paris rome.
r1 = tc { node = city, edge = road }.
r2 = tc { node = city, edge = road }.
%output r1.path.
?- r2.path berlin X.
```

```output
r1.path berlin paris.
r1.path berlin rome.
r1.path paris rome.
?- r2.path berlin X.
X = paris.
X = rome.
```

A functor's parameters may be formula functions and relations as well as modules. The following functor
selects the facts of a relation that satisfy a formula function.

```hugin,run
item : (name : string) -> (price : int) -> rel.
listed : item -> rel.
listed (item "pen" 2).
listed (item "lamp" 25).
cheap : item -> prop = [I] I.price < 10.
select (p : A -> prop) (r : A -> rel) = {
  sel : A -> rel.
  sel X :- r X, p X.
}.
bargains = select cheap listed.
%output bargains.sel.
```

```output
bargains.sel (item "pen" 2).
```

### Members without an instance

A meta member that mentions no object constant of its body, directly or through other members, does not
depend on an instance: `(f ā).m`, for a functor `f` applied to its arguments, is the member's definition
at the arguments, read from the functor's body without evaluating it, so no instance is created. A lemma
about the body's relations is such a member, since a judgment names the relations of its program by their
positions, not by their constants: `(walks G).walkTrans`, with `G` a variable, is the lemma at any graph,
and the same at a written graph creates no relation `walk`. A meta member that mentions an object
constant is read through an instance, as any member of an application is: one is created where the
application is evaluated with closed arguments.

## Signatures

```text
Signature   ::= "{" SigField ("," SigField)* "}"
SigField    ::= NAME ":" Type | "%complete" NAME
```

A *signature* is a record type used as the type of modules:
`graph : Type = { node : type, edge : node -> node -> rel }.` A field whose type is an object constant
type is matched by an object constant of that kind: a relation field by a relation, and a constructor
field `c : τ̄ -> a` by a constructor. A field `c : a` without columns is matched by a value of type `a`.
Signatures are [records](meta/records.md), and the rules of record subtyping apply: a module may have
more fields than the signature.

*Ascription* `m : sig = e.` gives the module `e` the type `sig`; the expression `(e : sig)` does the same
without a name. Ascription is *transparent*: the definition `m` unfolds to its value, so the types of the
signature are the types of `e` (`m.shape` is `e`'s `shape`), and a constructor of `e` stays a
constructor. Only the fields of `sig` are fields of `m`: it is an error ([E0906](errors/E0906.md)) to
select another. It is an error ([E0204](errors/E0204.md)) if `e` lacks a field of `sig` or a field has
another kind or type.

A field `%complete l` *requires* that the relation in the field `l` is
[complete](object/negation.md#completeness). A functor that negates or aggregates over a relation of its
parameter must require it; it is an error ([E0210](errors/E0210.md)) otherwise. It is an error
([E0208](errors/E0208.md)) to apply a functor to a module whose relation does not satisfy a requirement.

The following functor finds the nodes without outgoing edges. It negates the parameter's `edge`, so its
signature requires `%complete edge`.

```hugin,run
complete_graph : Type = { node : type, edge : node -> node -> rel, %complete edge }.
sinks (g : complete_graph) = {
  sink : g.node -> rel.
  sink N :- g.edge _ N, not g.edge N _.
}.
city : type. berlin, paris : city.
road : city -> city -> rel.
road berlin paris.
s = sinks { node = city, edge = road }.
%output s.sink.
```

```output
s.sink paris.
```

## Imports

```text
Import ::= "%import" STRING
```

`%import "path"` is an expression whose value is the module of another source file. The path is resolved
relative to the directory of the importing file; `.hgn` is appended if the path has no extension. A path
that starts with `std/` names a module of the standard library bundled with the compiler: `std/graph` is
the bundled file `std/graph.hgn`, whatever the importing file. A definition `geo = %import "lib/geo".`
binds the module, and `geo.place` selects a member.

A file is elaborated and evaluated once per compilation, however often it is imported, so every importer
sees the same object constants. The object constants of an imported file are named after the file:
`geo.here` for the constant `here` of `lib/geo.hgn` (`geo2.here` if two imported files have the same
name). An imported file sees the prelude, and the files it imports itself, but not the program that
imports it. The import graph must be acyclic. It is an error ([E0108](errors/E0108.md)) if an imported
file does not exist or if imports form a cycle.

The following program imports a library and uses its type and relation. It is not checked, since it
needs the file `lib/geo.hgn`.

```hugin,ignore
geo = %import "lib/geo".
reachable : geo.place -> rel.
reachable X :- geo.near X.
```

An import may be ascribed a signature, which hides the other members of the file. The following
definition is not checked either.

```hugin,ignore
shapes_sig : Type = { shape : type, dot : shape, square : int -> shape, area : shape -> int -> rel }.
s : shapes_sig = %import "lib/shapes".
```

The following program imports a file that does not exist.

```hugin,compile_fail,E0108
lib = %import "missing".
```

The following program imports a module of the standard library that does not exist.

```hugin,compile_fail,E0108
lib = %import "std/geometry".
```

### Export signatures

```text
Export ::= "%export" Atom "."
```

A file's module is the record of its declarations. An *export signature* `%export S.` replaces it with
the ascription `(file : S)`: an import of the file has exactly the fields of the signature `S`, and the
other declarations of the file are not fields of it. Ascription is transparent, so the exported types,
constructors and relations are those of the file. A declaration that `S` leaves out still exists: its
rules are evaluated and its facts keep their identity. `S` is elaborated after the declarations of the
file and may refer to them. A file without `%export` exports all of its declarations.

It is an error ([E0204](errors/E0204.md)) if the file does not match its export signature, and
([E0110](errors/E0110.md)) if a file has more than one `%export` or a module body has one.

The following file exports `area` but not its helper `square`, so an importer that selects `square` gets
an error ([E0906](errors/E0906.md)). It is not checked, since its point is what an importer of it sees.

```hugin,ignore
%export { area : int -> int }.
area : int -> int.
area R = 3 * square R.
square : int -> int.
square N = N * N.
```

The following file has two export signatures.

```hugin,compile_fail,E0110
%export { width : int }.
%export { height : int }.
width : int = 3.
height : int = 4.
size : int -> rel.
size (width * height).
```

## Opening modules

```text
Use ::= "%use" (STRING | Atom) ("(" NAME ("," NAME)* ")")? "."
```

An item `%use m.` *opens* the module `m`: the fields of `m` become names of the file. `m` is an atom: a
name, a path or a parenthesised expression whose value is a module; `%use "path".` opens the file `path`,
as `%use %import "path".` does. With a list of names, `%use m (x, y).` opens only those fields; it is an
error ([E0906](errors/E0906.md)) if one is not a field of `m`.

The fields are those of the type of `m`, so a signature decides what is opened: `%use` of a file opens
its export signature, and `%use (m : sig).` opens the fields of `sig`. An opened name denotes the field:
a constructor stays a constructor, also in patterns, and a relation the same relation. `%use` may come
before the definition of the module it opens. It is an error ([E0107](errors/E0107.md)) if `m` is not a
module, and ([E0907](errors/E0907.md)) to write `%use` in a module body. A `%use` that is left out for an
error opens nothing, and a name that it might have opened (any name for `%use m.`, the names listed for
`%use m (x, y).`) is not reported as unresolved ([E0101](errors/E0101.md)): the error is the `%use`'s.

The following program opens a module value and then the relation of a functor's instance.

```hugin,run
metric = { unit : string = "km". factor : int = 1000. }.
%use metric.
graph : Type = { node : type, edge : node -> node -> rel }.
tc (g : graph) = {
  path : g.node -> g.node -> rel.
  path X Y :- g.edge X Y.
  path X Z :- g.edge X Y, path Y Z.
}.
city : type. berlin, paris, rome : city.
road : (from : city) -> (to : city) -> (length : int) -> rel.
road berlin paris 1054. road paris rome 1421.
edge : city -> city -> rel.
edge X Y :- road X Y _.
%use (tc { node = city, edge = edge }).
metres : string -> city -> int -> rel.
metres unit Y M :- road berlin Y L, M = L * factor.
?- path berlin X.
%output metres.
```

```output
metres "km" paris 1054000.
?- path berlin X.
X = paris.
X = rome.
```

Names opened by `%use` are shadowed by the declarations of the file, in the whole file. It is an error
([E0109](errors/E0109.md)) to use a name that two `%use` items open for different declarations, unless
they are all meta constants (see [Overloaded opened names](#overloaded-opened-names)); opening the same
declaration twice is not an error. The following program opens the relation `path` of two instances.

```hugin,compile_fail,E0109
graph : Type = { node : type, edge : node -> node -> rel }.
tc (g : graph) = {
  path : g.node -> g.node -> rel.
  path X Y :- g.edge X Y.
}.
city : type. berlin, paris : city.
road : city -> city -> rel.
road berlin paris.
rail : city -> city -> rel.
%use (tc { node = city, edge = road }).
%use (tc { node = city, edge = rail }).
?- path berlin X.
```

### Overloaded opened names

A name that `%use` items open for several declarations that are all meta constants (functions,
definitions, constructors and postulates of the meta level, also meta types) is *overloaded*: a use of
it denotes one of them, chosen by the types as an [operator bound to several meta
functions](lexical-structure.md#operators-bound-to-meta-functions) is. For a use `n a₁ … aₖ` (`k ≥ 0`
explicit arguments):

1. A candidate whose type takes fewer than `k` explicit arguments is left out, and so is one whose result
   after the `k` arguments has a head that differs from the expected type's (a type constructor, a base
   type, a universe, a function type, `⇑`, a record type, `rel` or `prop`). A head that is not known (an
   unsolved type, a stuck type-level application) fits every candidate.
2. If several remain and `k ≥ 1`, the first argument is inferred, and a candidate whose first explicit
   domain has a head that differs from that of the argument's type is left out.

Each argument is elaborated once, and nothing is undone: the chosen candidate is applied as if it were
written alone, and its arguments are then checked against its type. It is an error
([E0932](errors/E0932.md)) if several candidates remain, and ([E0933](errors/E0933.md)) if none does.
Object constants (relations, object types and constructors, also those of a module instance) are never
overloaded: a name opened for an object constant and another declaration is ambiguous (E0109). A
declaration of the file still shadows the opened names, and a name that only one `%use` opens is not
overloaded. In an editor, hover and go to definition show the chosen constant.

The following program opens `decide` of [`std/semantics`](std/semantics.md) (a derivation by evaluation)
and the generic `decide` of [`std/decide`](std/decide.md) (a decider's proof). The first use expects a
[judgment](std/semantics.md#the-judgment-notation), the result of the semantics' `decide` after two
arguments; the second applies three arguments, which only the generic `decide` takes.

```hugin,run
%use "std/eq" (eq, tt).
%use "std/nat".
%use "std/decide".
%use "std/semantics".
city : type. berlin, paris : city.
trip = { hop : city -> city -> rel. hop berlin paris. }.
direct : trip ⊢ hop berlin paris = decide 1 tt.
same : eq (plus 2 2) 4 = decide natEqual { fst = plus 2 2, snd = 4 } tt.
%opaque direct same.
proved : string -> rel.
proved "both".
%output proved.
```

```output
proved "both".
```

`%use` and `%export` are not directives (meta functions): they change scopes and the module of a file,
which no meta function can.

> **Note.** A file that the [prelude](prelude.md) opens with a selective `%use "f" (x, …)` and that
> declares no object constants (only meta declarations, definitions and functions; no object type,
> relation, constructor, shared data, rule or module instance) is elaborated only for a program that may
> use one of the names opened from it, such as `std/demand` for a program that writes `%demand`. A file
> that does declare object constants is always elaborated. Since such a file creates nothing that the
> object program contains, a program cannot tell the difference: its meaning, output and diagnostics are
> the same either way. Only compile time changes. The files that such a file imports are elaborated with
> it, or as the program's own imports if the program imports them (`std/list`, which `std/demand`
> imports): their constants are reachable only through one of the two.


## Scopes

The scopes of a compilation are nested as follows: the prelude encloses every file; each file is a scope
of its own; each module body is a scope inside the scope where it is written. The names that a file opens
with `%use` lie between the file and the enclosing scope; a name opened for several meta constants is
[overloaded](#overloaded-opened-names), and one opened for several declarations of which one is an object
constant is ambiguous ([E0109](errors/E0109.md)). A name declared in a scope shadows the same
name of an enclosing scope, in the whole scope, also before its declaration. The names the prelude opens
are in scope in every file. When a program declares an object constant with the name of a constant of the
prelude or of the standard library, that constant is displayed as `prelude.n`.
