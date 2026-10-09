# The standard library

The *standard library* is the set of modules bundled with the compiler under the path `std/`. A program
imports a module with `%import "std/m"` or opens it with `%use "std/m".`
([Modules](../modules.md#imports)): an import path that starts with `std/` names a bundled module,
whatever the importing file. The [prelude](../prelude.md) opens a few names of these modules in every
file.

| module | contents |
|---|---|
| [`std/reflect`](reflect.md) | lists, options and booleans; object syntax as data; declarations as data and the primitive directives; the primitive operations on symbols |
| [`std/list`](list.md) | relations over the lists that are facts |
| [`std/graph`](graph.md) | the signature of graphs and functors over it |
| [`std/demand`](demand.md) | the directive `%demand` |

The object constants of the standard library are named without a prefix, as those of the prelude: the
relation `len` of `std/list` is `len`, not `list.len`. When a program declares an object constant with
the name of one of them, the library's constant is displayed as `prelude.n`.

The compiler knows the declarations of `std/reflect` by name: quotes, list syntax, mode items, typed
holes and the footprints of directives use the declarations of that file, whatever names a program
declares or opens. A program may therefore declare its own `term`, `list` or `output`.
