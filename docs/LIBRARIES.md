# Libraries, imports and the prelude

This note describes how a Hugin program is split over several files, how the standard library is
provided, and how this relates to the module system of Section 4. It addresses issue #6.

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

### Contents

| names | what |
|---|---|
| `int`, `float`, `string` | base types |
| `list A`, `nil`, `cons`, `len` | lists (fact constructors) and their length: `len : (l : list A) -> (n : int) -> rel` measures the lists that are facts (guarded induction on the list); with `%demand len +l -n.` in a program a call demands its list, and the demand rule makes the list a fact (Section 13.3, REDESIGN §7.4) |
| `option A`, `none`, `some` | optional values |
| `pair A B` | a struct family with labels `fst`, `snd` |
| `graph`, `tc`, `bounded` | the graph signature and functors of Section 13.1 |
| `seq A`, `snil`, `scons`, `sappend` | meta lists, written `[]`, `[a, b]` and `x :: xs` |
| `sym`, `term`, `formula`, `rule`, `item`, `module` | reflection (docs/REDESIGN.md §6.8): object syntax as data, with their constructors (`tvar`, `tapp`, `fatom`, `horn`, `irule`, `inamed`, `ierror`, …) and `openT`/`openF`, which instantiate the variable an aggregate binds (docs/NOTES.md, "Reflection") |
| `decl`, `attr`, `measure`, `attach` | declarations as data, with the attributes the primitive directives attach (docs/REDESIGN.md §7; docs/NOTES.md, "Directives") |
| `input`, `output`, `open`, `derivations`, `terminates` | the primitive directives (`%input r.`, …): meta functions returning a `decl` |

## Diagnostics

Spans carry their source file, so diagnostics in an imported file point into that file. A file is
checked once, independently of how often it is imported. Errors in generated code carry the meta-level
call chain as before; a call chain may cross files.

## The query layer

Imported files are read through the `SourceText` input of the query database, so they are parsed once
and an edit to a library invalidates exactly the programs that import it. The prelude and imported files
are also named and elaborated by queries (`NameLibrary`, `ElabLibrary`), once per database revision:
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

* **Hiding.** Only the signature's fields are visible through `s`; using another export is E0101.
* **Transparent.** Ascription is coercive but not sealing: `s.shape` is the file's `shape`, so values flow
  freely between `s` and any other import of the same file.
* **Constructor fields.** A field `c : τ̄ -> a` whose domain and result are object types (Section 2.5)
  denotes a constructor, not a meta function, so `s.square N` builds terms from object variables; every
  constructor is a fact constructor, whose facts the importer (or a functor) may read. A relation field is
  matched only by a relation.
* **Constants.** A nullary constructor `dot : shape.` of the file also matches a value field `dot : shape`.
* Mismatches (missing field, wrong arity, relation versus constructor, wrong type) are E0204 with the reason as a note.

## Not (yet) done

* **Sealing.** An opt-in opaque ascription that makes the signature's types abstract. It needs
  generative abstract types at evaluation (fresh object types standing for the hidden ones) and is left
  for later; transparent ascription already covers hiding.
* **Separate compilation.** Every process elaborates the prelude and the imported files from source
  (once, when they are first used).
  The interface of a compiled library would be its signature, its object declarations, and its families
  as generic templates (monomorphization must happen in the client so that family instances are shared,
  Section 4.6). Within one process the query database already shares parsing and elaboration.
* **Build manifest.** A project file with source roots, dependencies and default facts; a search path for
  imports of installed libraries (`%import "std/graphs"`).
* **Aggregates as library functions** (Section 14, future work) would move `count`, `sum`, `min`, `max`
  into the prelude; this needs higher-order formula functions over aggregates and is left open.
