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
see the body's members, the parameters of an enclosing functor and the names of the file.

It is an error ([E0907](errors/E0907.md)) to use in a module body: refinements, families of object
constants, reflected items `$e.`, and additive or module-wide directives. It is an error
([E0107](errors/E0107.md)) to select a member of a value that is not a module.

## Instances

A module body is *generative*: evaluating it creates fresh object constants for the object constants it
declares, and stages its rules and queries with them. A definition `m = { … }.` or `m = f a.` is
evaluated once, so all uses of `m` share one *instance*. Two definitions that evaluate the same body,
also by applying a functor to the same arguments, create two instances with distinct relations.

The object constants of an instance are named after the definition that created it: the relation `path`
of the instance `r1` is `r1.path`. An instance that no definition names is called `_m1`, `_m2`, …; a name
that repeats gets a suffix `#k`.

## Functors

A *functor* is a meta function that returns a module, written as a definition with parameters whose
right-hand side is a module body: `tc (g : graph) = { … }.` Its parameters are typed by
[signatures](#signatures). An application `tc { node = city, edge = road }` evaluates the body with the
parameter bound to the argument, and creates an instance.

The following program applies the prelude's functor `tc` (transitive closure) twice to the same graph.
The two applications create two distinct relations `r1.path` and `r2.path`.

```hugin,run
city : type. berlin : city. paris : city. rome : city.
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

*Ascription* `m : sig = e.` gives the module `e` the type `sig`. It is transparent: the types of the
signature are the types of `e` (`m.shape` is `e`'s `shape`), but only the fields of `sig` are visible
through `m`. It is an error ([E0204](errors/E0204.md)) if `e` lacks a field of `sig` or a field has
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
city : type. berlin : city. paris : city.
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
relative to the directory of the importing file; `.hgn` is appended if the path has no extension. A
definition `geo = %import "lib/geo".` binds the module, and `geo.place` selects a member.

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

## Scopes

The scopes of a compilation are nested as follows: the prelude encloses every file; each file is a scope
of its own; each module body is a scope inside the scope where it is written. A name declared in a scope
shadows the same name of an enclosing scope, in the whole scope, also before its declaration. When a
program declares an object constant with the name of a prelude constant, the prelude's constant is
displayed as `prelude.n`.
