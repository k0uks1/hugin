# `std/demand`

The module `std/demand` defines the directive `%demand` ([Directives](../directives.md#demand)). Its
[export signature](../modules.md#export-signatures) has one field:

```hugin,ignore
%export { demand : (r : sym) -> modes (labels r) -> module -> module }.
```

`demand` is a module-wide directive written in Hugin with quoted patterns, on
[`std/list`](list.md) and the binding analysis of [`std/directives`](directives.md). Its helper functions,
the transformation step by step and the pruning of the prefixes of demand rules, are declarations of the
module that its signature leaves out, so they are not fields of `std/demand`. The
[prelude](../prelude.md) opens `demand`, so `%demand` is available in every program.

The following program makes `reach` demand-driven: it is computed only from the node that the query
asks for and the nodes reached from it: `reach 5 6` is not derived.

```hugin,run
edge : int -> int -> rel.
edge 1 2. edge 2 3. edge 5 6.
reach : (from : int) -> (to : int) -> rel.
%demand reach +from -to.
reach X Y :- edge X Y.
reach X Z :- edge X Y, reach Y Z.
?- reach 1 Y.
%output reach.
```

```output
reach 1 2.
reach 1 3.
reach 2 3.
?- reach 1 Y.
Y = 2.
Y = 3.
```

A module that imports `std/demand` sees `demand` only: a helper is not a field
([E0906](../errors/E0906.md)).

```hugin,compile_fail,E0906
d = %import "std/demand".
x = d.dmodule.
```
