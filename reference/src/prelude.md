# The prelude

The *prelude* is a Hugin file bundled with the compiler, `<stdlib>/prelude.hgn`. It is included in every
program unless the option `--no-prelude` is given. Its scope encloses every file of a compilation, so the
names it declares or [opens](modules.md#opening-modules) are in scope everywhere without an import, and a
program may shadow any of them ([Modules](modules.md#scopes)). The prelude holds only what nearly every
program uses; everything else is in the modules of the [standard library](std/index.md), which a program
imports.

The prelude consists of two `%use` items:

```hugin,ignore
%use "std/reflect" (
  bool, true, false, if, same, list, nil, cons, append, option, none, some,
  input, output, open, derivations, terminates
).
%use "std/demand" (demand).
```

So the names in scope in every file are:

| names | what | defined in |
|---|---|---|
| `int`, `float`, `string` | the base types, built into the compiler | [Object types](object/types.md#base-types) |
| `bool`, `true`, `false`, `if` | booleans, shared by both stages, and the choice between two values | [`std/reflect`](std/reflect.md#lists-options-and-booleans) |
| `same` | equality of symbols and literals (primitive) | [`std/reflect`](std/reflect.md#primitives) |
| `list`, `nil`, `cons`, `append` | lists, shared by both stages, and the concatenation of meta lists | [`std/reflect`](std/reflect.md#lists-options-and-booleans) |
| `option`, `none`, `some` | optional values, shared by both stages | [`std/reflect`](std/reflect.md#lists-options-and-booleans) |
| `%input`, `%output`, `%open`, `%derivations`, `%terminates` | the primitive directives | [Directives](directives.md#the-primitive-directives) |
| `%demand` | demand-driven evaluation | [Directives](directives.md#demand), [`std/demand`](std/demand.md) |

`int`, `float` and `string` are in scope in every program that includes the prelude. A program compiled
with `--no-prelude` declares the base types it uses ([Object types](object/types.md#base-types)), and it
may import modules of the standard library itself.

The following program uses only names of the prelude: a meta list, `if`, `same` and `%output`.

```hugin,run
evens : list int -> list int.
evens [] = [].
evens (X :: Xs) = if (same (X - X / 2 * 2) 0) (X :: evens Xs) (evens Xs).
picked : list int -> rel.
picked (evens [1, 2, 3, 4]).
%output picked.
```

```output
picked (cons 2 (cons 4 nil)).
```
