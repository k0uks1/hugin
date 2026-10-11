# The standard library

The *standard library* is the set of modules bundled with the compiler under the path `std/`. A program
imports a module with `%import "std/m"` or opens it with `%use "std/m".`
([Modules](../modules.md#imports)): an import path that starts with `std/` names a bundled module,
whatever the importing file. The [prelude](../prelude.md) opens a few names of these modules in every
file.

| module | contents |
|---|---|
| [`std/reflect`](reflect.md) | lists, options and booleans; object syntax as data; declarations as data and the primitive directives; the primitive operations on symbols |
| [`std/nat`](nat.md) | the natural numbers of the meta level, `plus` and `toInt` |
| [`std/list`](list.md) | functions over meta lists, natural numbers as fuel, relations over the lists that are facts |
| [`std/directives`](directives.md) | the parts of rules and modules, the calls of a relation, the binding analysis, fresh names and errors, for directive authors |
| [`std/graph`](graph.md) | the signatures of graphs; transformers, closures, reachability, components, degrees and distances as functors |
| [`std/order`](order.md) | the best items by a score, rankings and top-k; the order of a finite set of numbers |
| [`std/demand`](demand.md) | the directive `%demand` |

The object constants of the standard library are named without a prefix, as those of the prelude: the
relation `len` of `std/list` is `len`, not `list.len`. When a program declares an object constant with
the name of one of them, the library's constant is displayed as `prelude.n`.

The compiler knows the declarations of `std/reflect` by name: quotes, list syntax, mode items, typed
holes and the footprints of directives use the declarations of that file, whatever names a program
declares or opens. A program may therefore declare its own `term`, `list` or `output`.
