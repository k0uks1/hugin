# `std/graph`

The module `std/graph` defines the signature of graphs and functors that derive relations of a graph.

| declaration | meaning |
|---|---|
| `graph : Type = { node : type, edge : node -> node -> rel }.` | the signature of graphs |
| `tc (g : graph)` | a functor: its relation `path` is the transitive closure of `g.edge` |
| `bounded (g : graph) (limit : int)` | a functor: its relation `hop X Y N` holds if there is a walk of `N` edges from `X` to `Y`, for `N ≤ limit` |

The following program applies both functors to a graph of three cities.

```hugin,run
%use "std/graph".
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
