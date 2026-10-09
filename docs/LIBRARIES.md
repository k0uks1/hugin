# Libraries, imports and the prelude

This note describes how a Hugin program is split over several files, how the standard library is
provided, and how this relates to the module system of Section 4 of the definition draft. It addresses
issue #6. The normative description is the reference chapter [Modules, functors and libraries](https://k0uks1.github.io/hugin/modules.html)
and [The prelude](https://k0uks1.github.io/hugin/prelude.html); this note records the design and its implementation.

## Files are module bodies

A source file is a module body in the sense of rule M-Body (Section 4.3): a sequence of items
elaborated in a fresh scope. The expression

```
geo = %import "lib/geo".
```

is a meta expression whose value is the module value of the file `lib/geo.hgn` and whose meta type is the
signature of that body's exports: object declarations, type definitions and meta definitions without
parameters, exactly as for `geo = { ... }.` written inline. Everything that works for a module-valued
definition therefore works for an import: paths `geo.place`, passing `geo` to a functor whose parameter
signature it matches, and so on.

The import path is a string literal resolved relative to the directory of the importing file. If the path
has no extension, `.hgn` is appended.

## One evaluation per file

Module bodies are generative (Section 4.5): two occurrences of `{ place : type. }` declare two distinct
types. If an import were a textual copy of the body, a file imported twice (directly and through another
library) would declare its types twice, and the two importers could not exchange values. Instead, a file
is elaborated and evaluated **once per compilation**, and every `%import` of it denotes that single module
value. Generativity is preserved within a file; across files, identity is the file's resolved path.
(Elaboration is even shared between compilations, see below; evaluation, which names the file's object
declarations, happens once per compilation.)

Consequently the files of a compilation form a directed graph that must be acyclic: a file is elaborated
before the files that import it, which matches the rule that meta definitions may only refer to earlier
definitions (Section 2.3). A cycle is reported as E0108 together with the cycle. A missing file is also
E0108; the import then has the erroneous meta type, so uses of it do not cause further errors.

## Scoping

An imported file sees the prelude but neither the program nor other files, unless it imports them
itself. A library is therefore closed: its meaning does not depend on who imports it. The scopes are

```
prelude
├── program
├── file lib/geo.hgn
└── file lib/routes.hgn
```

Object declarations of an imported file are named with the file's name as prefix (`geo.here`), like the
fresh prefixes of module bodies. If two imported files have the same name (in different directories),
the second gets a numbered prefix (`geo2`).

## The prelude

The prelude is the file [`<stdlib>/prelude.hgn`](../src/main/resources/hugin/stdlib/prelude.hgn), bundled
with the compiler as a resource and included in every compilation unless `--no-prelude` is given. Its
scope encloses the scopes of all files, so its names are visible everywhere without an import, and a
program may shadow them (e.g. declare its own `list`). When the program declares a name that the prelude
also declares, the prelude's object declaration is named `prelude.n` so that the two remain distinct.

The prelude's declarations get no prefix: `len[int]` and `roads.path` print as before. Its generic
declarations (families such as `list A`, functors such as `tc`) cost nothing unless they are used,
because families are instantiated only at the types they are used at (Section 4.6) and functors are
evaluated only when applied.

### Base types

`int`, `float` and `string` are built into the meta level (docs/REDESIGN.md Q2): they are in scope in
every file that is compiled with the prelude. A program compiled without the prelude (`--no-prelude`)
declares the base types it uses:

```
int : type = %builtin int.
```

`%builtin b` names a base type provided by the implementation. It is allowed only as the definition of
a type declaration (E0103 otherwise); the declared name is free, so `num : type = %builtin int.` declares
another name for the same base type. Base types are printed by their builtin names. Keywords (`type`,
`rel`, `prop`, `Type`), primitive formulas and aggregates remain part of the language.

### Contents (#61, batch B1)

The standard library is split (design: `docs/design/stdlib.md`):

| file | contents |
|---|---|
| `<stdlib>/prelude.hgn` | two `%use` items: `bool`, `true`, `false`, `if`, `same`, `list`, `nil`, `cons`, `append`, `option`, `none`, `some` and the primitive directives from `std/reflect`, `demand` from `std/demand` |
| `<stdlib>/std/reflect.hgn` | what the compiler knows by name: `list`, `option` (shared), `bool`, `if`, the reflective types, `quoted`, `decl`/`attr`/`measure`, the primitive directives, `modes`, the primitives `same`, `labels`, `derive`, `derived` |
| `<stdlib>/std/demand.hgn` | `%demand` (`%export { demand : … }`; its helpers are outside the signature) |
| `<stdlib>/std/list.hgn` | `len` |
| `<stdlib>/std/graph.hgn` | `graph`, `tc`, `bounded` |

`pair` was deleted (no program used it; meta code uses record types).

**The prelude's chain.** The prelude imports `std/reflect` and `std/demand`, which the import graph
places before it (the walk visits the prelude's imports first). They are elaborated as libraries with no
enclosing scope (`std/demand` opens `std/reflect` itself), then the prelude on top of them
(`ProgramElab.preludeChain`); the names the prelude opens are its scope for every later file. The chain
is shared per process by `StdlibCache.prelude(chain)`, keyed by every file's text, and memoised as one
step by the query `ElabLibrary` (a chain key ending in the prelude). The constants of `<stdlib>/` files
have no qualifier (`len`, not `list.len`) and are displayed as `prelude.n` when the program declares the
same name (`ObjectSymbols`).

**Compiler-known names by file.** `ReflectiveGlobals`, the typed quotes (`quoted`, `qterm`, `raw`) and the
mode items (`modes`) are looked up in the module of `<stdlib>/std/reflect.hgn` when the compilation
includes it (`Reflective.coreName`), else in the prelude's scope, else in the file (the core tests
concatenate a prelude into their programs). A program's own `term` or `list` never changes what quotes,
list syntax or mode items build. With `--no-prelude`, `std/reflect` is part of the compilation only if the
program imports it.

**Migration.** Programs that name reflective types or constructors open `std/reflect`; those that use
`tc`, `bounded` or `graph` open `std/graph`, those that use `len` open `std/list`. In negative and
recovery tests the `%use` item is on the line that ends the leading comment, so that the lines of the
diagnostics do not move. The REPL's `:imports` leaves out the prelude's chain.

### Shared `bool` (#61, batch B3)

`bool : data.` in `std/reflect`: `true` and `false` are shared constructors, so `bool` is also an object
type, for data with boolean columns (reference: `std/reflect`). The meta `bool` and its uses (`if`,
`same`, `derived`) do not change; a meta boolean is used as an object `bool` where one is expected
(`bool.lift`). There is still no formula `true` or `false`: a constant used as a formula is an atom of its
constructor, which holds if the constant is a fact. W0008 (lint `constant_formulas`, on by default,
`obj/typing/ConstFold.scala`) reports every constant without arguments used as a formula of a body or a
query, also under `not`, in aggregates and in disjunctions (reference: rules, "Constants as formulas").

Consequences: every staged program declares `bool : type.`, `true : bool.` and `false : bool.` (as it
declares every object constant it includes), which `--print-after stage` shows; and a declaration
`x : bool.` outside `std/reflect` is a constructor of the closed type `bool` (E0923), so a meta postulate
of type `bool` is no longer possible (`neg/e0909_stuck_shared` postulates a `term` instead).

## Diagnostics

Spans carry their source file, so diagnostics in an imported file point into that file. A file is
checked once, independently of how often it is imported. Errors in generated code carry the meta-level
call chain as before; a call chain may cross files.

## The query layer

Imported files are read through the `SourceText` input of the query database, so they are parsed once
and an edit to a library invalidates exactly the programs that import it. The prelude and imported files
are also elaborated by queries (`ElabLibrary`), once per database revision:
compilations in the same database (the REPL's inputs, the files open in the language server) share
them, and editing a program does not elaborate its libraries again. Their results are frozen and read by
the importing compilations; only the evaluation of the meta level runs per compilation. A `SourceText`
that was never set is read on first use (from the bundled standard library for `<stdlib>/` paths,
otherwise from disk); an editor sets the text of open files explicitly.

The bundled standard library is shared further, by the whole process (`compiler/StdlibCache.scala`,
issue #60): a `<stdlib>/` file is parsed once per text, and the prelude elaborated once per text (and
`builtinNames` flag), for every database and every direct compilation in the JVM (each test, each CLI
command). The cache is keyed by the whole text, so an edited prelude is elaborated again; an elaborated
prelude is used only with the very parse it came from (its positions point into it), and later parts
only fork it. `StdlibCacheSuite` compares compilations with and without the cache. Imported files of a
program are not cached beyond their database (see `docs/PERFORMANCE.md`).

## Interfaces

A file needs no interface: `geo = %import "lib/geo".` exposes everything the file exports. Optionally,
an import is ascribed a signature, which is checked like any ascription of a module value:

```
shapes_sig : Type = { shape : type, dot : shape, square : int -> shape, area : shape -> int -> rel }.
s : shapes_sig = %import "lib/shapes".
```

* **Hiding.** Only the signature's fields are visible through `s`; using another export is E0906 (no field).
* **Transparent.** Ascription is coercive but not sealing: `s.shape` is the file's `shape`, so values flow
  freely between `s` and any other import of the same file.
* **Constructor fields.** A field `c : τ̄ -> a` whose domain and result are object types (Section 2.5)
  denotes a constructor, not a meta function, so `s.square N` builds terms from object variables; every
  constructor is a fact constructor, whose facts the importer (or a functor) may read. A relation field is
  matched only by a relation.
* **Constants.** A nullary constructor `dot : shape.` of the file also matches a value field `dot : shape`.
* Mismatches (missing field, wrong arity, relation versus constructor, wrong type) are E0204 with the reason as a note.

### Export signatures and `%use` (#61, batch B0)

A file states its own interface with `%export S.`: its module value is `(file : S)`, the same transparent
ascription as `s : S = %import "f"` at an importer, so every importer sees only the fields of `S`
(`core/elab/Uses.scala`). The signature is elaborated after the file's declarations; a second `%export`,
or one in a module body, is E0110; a file that does not match is E0204 with a note. This is the one
addition the standard library needs for hiding (`docs/design/stdlib.md`, 4.5): the helpers of a module are
outside its signature, with no `private` modifier and no interface file.

`%use m.` opens the fields of the module `m` (of its type, so a signature decides) into the file's scope;
`%use m (x, y).` only those named; `%use "f".` opens a file (the parser makes the path an `Import`, so the
import graph sees it). An opened name denotes the global the field is (an import's fields are globals, so
constructors stay constructors in patterns); a field that is not a declaration (a member of a module
instance) is opened as a hidden definition equal to the projection. Opened names lie between the file's
declarations (which shadow them in the whole file) and the prelude; a name opened for two globals is E0109
where it is used. `%use` items are elaborated first among the declarations, and an item whose name is
unresolved is retried while a `%use` is pending, so `%use m.` may come before `m = %import "f".` The
names the prelude opens are part of the prelude's scope (`ProgramElab.prelude`), which is how the prelude
re-exports from other files (batch B1).

Import paths that start with `std/` denote `<stdlib>/std/…` (`SourceLoader.resolve`), whatever the
importing file; a path that leaves `std/` after normalisation is an ordinary relative path.

## Not (yet) done

* **Sealing.** An opt-in opaque ascription that makes the signature's types abstract. It needs
  generative abstract types at evaluation (fresh object types standing for the hidden ones) and is left
  for later; transparent ascription already covers hiding.
* **Separate compilation.** Every process elaborates the prelude and the imported files from source
  (once, when they are first used).
  The interface of a compiled library would be its signature, its object declarations, and its families
  as generic templates (instances must be created in the client so that family instances are shared,
  Section 4.6). Within one process the query database already shares parsing and elaboration.
* **Build manifest.** A project file with source roots, dependencies and default facts; a search path for
  imports of installed libraries (the bundled standard library has the fixed prefix `std/`).
* **Aggregates as library functions** (Section 14, future work) would move `count`, `sum`, `min`, `max`
  into the prelude; this needs higher-order formula functions over aggregates and is left open.
