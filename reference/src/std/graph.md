# `std/graph`

The module `std/graph` defines the signatures of graphs and functors over them. A functor that
transforms a graph returns a module with the fields `node` and `edge`, so its result is a graph again
and composes with every functor: `rtc (undirected g)` is the equivalence closure of `g`. A program opens
the module with `%use "std/graph".`

| declaration | meaning |
|---|---|
| `graph : Type = { node : type, edge : node -> node -> rel }.` | the signature of graphs |
| `complete_graph : Type = { node : type, edge : node -> node -> rel, %complete edge }.` | graphs whose edges are [complete](../object/negation.md#completeness) |
| `weighted : Type = { node : type, edge : node -> node -> int -> rel }.` | graphs with a weight on each edge |
| `reverse (g : graph)` | the graph with every edge reversed: `edge Y X` for `g.edge X Y` |
| `undirected (g : graph)` | the symmetric closure: `edge X Y` and `edge Y X` for `g.edge X Y` |
| `vertices (g : graph)` | `vertex X` for every node with an edge |
| `tc (g : graph)` | `path X Y` if there is a walk of one edge or more from `X` to `Y` (the transitive closure) |
| `rtc (g : graph)` | `path X Y` for the walks of `tc`, and `path X X` for every vertex (the reflexive transitive closure) |
| `reach (g : graph) (seed : g.node -> rel)` | `reached X` for the nodes reachable from a seed, the seeds included |
| `scc (g : graph)` | `same X Y` if `X` and `Y` reach each other (strongly connected components) |
| `degrees (g : complete_graph)` | `source`, `sink`, `out_degree X N` and `in_degree X N` for the vertices |
| `shortest (g : weighted)` | `dist X Y D`: the least sum of weights `D` of a walk from `X` to `Y` |
| `hops (g : graph)` | `dist X Y D`: the least number of edges `D` of a walk from `X` to `Y` |
| `bounded (g : graph) (limit : int)` | `hop X Y N` if there is a walk of `N` edges from `X` to `Y`, for `N ≤ limit` |

The instances of composed functors are named as [Modules](../modules.md#instances) describes: the
application that a definition names takes the definition's name, an instance that a member of a body
names takes the member's path, and an instance passed as an argument is anonymous (`_m1`).

## Transformers

`reverse` reverses the edges of a graph. The following program finds the predecessors of `c`.

```hugin,run
%use "std/graph".
city : type. a, b, c : city.
road : city -> city -> rel.
road a b. road b c.
back = tc (reverse { node = city, edge = road }).
?- back.path c X.
```

```output
?- back.path c X.
X = a.
X = b.
```

`undirected` adds the reverse of every edge. With `rtc` it gives the weakly connected components.

```hugin,run
%use "std/graph".
city : type. a, b, c, d : city.
road : city -> city -> rel.
road a b. road c b. road d d.
weak = rtc (undirected { node = city, edge = road }).
?- weak.path a X.
```

```output
?- weak.path a X.
X = a.
X = b.
X = c.
```

`vertices` gives the nodes that have an edge.

```hugin,run
%use "std/graph".
city : type. a, b, c : city.
road : city -> city -> rel.
road a b.
v = vertices { node = city, edge = road }.
%output v.vertex.
```

```output
v.vertex a.
v.vertex b.
```

## Closures and reachability

`tc` is the transitive closure.

```hugin,run
%use "std/graph".
city : type. berlin, paris, rome : city.
road : city -> city -> rel.
road berlin paris. road paris rome.
roads = tc { node = city, edge = road }.
%output roads.path.
```

```output
roads.path berlin paris.
roads.path berlin rome.
roads.path paris rome.
```

`rtc` adds a walk of no edges from every vertex to itself.

```hugin,run
%use "std/graph".
city : type. berlin, paris : city.
road : city -> city -> rel.
road berlin paris.
roads = rtc { node = city, edge = road }.
%output roads.path.
```

```output
roads.path berlin berlin.
roads.path berlin paris.
roads.path paris paris.
```

`reach` follows the edges from the nodes of a seed relation.

```hugin,run
%use "std/graph".
city : type. a, b, c, d : city.
road : city -> city -> rel.
road a b. road b c. road d a.
start : city -> rel.
start a.
fromA = reach { node = city, edge = road } start.
%output fromA.reached.
```

```output
fromA.reached a.
fromA.reached b.
fromA.reached c.
```

`scc` relates the nodes that reach each other.

```hugin,run
%use "std/graph".
city : type. a, b, c : city.
road : city -> city -> rel.
road a b. road b c. road c b.
s = scc { node = city, edge = road }.
%output s.same.
```

```output
s.same a a.
s.same b b.
s.same b c.
s.same c b.
s.same c c.
```

## Degrees and distances

`degrees` needs a complete graph, since it negates and counts edges. A source is a vertex without
incoming edges, a sink one without outgoing edges.

```hugin,run
%use "std/graph".
city : type. a, b, c, d : city.
road : city -> city -> rel.
road a b. road b c. road d c.
dg = degrees { node = city, edge = road }.
%output dg.source. %output dg.sink. %output dg.out_degree. %output dg.in_degree.
```

```output
dg.in_degree a 0.
dg.in_degree b 1.
dg.in_degree c 2.
dg.in_degree d 0.
dg.out_degree a 1.
dg.out_degree b 1.
dg.out_degree c 0.
dg.out_degree d 1.
dg.sink c.
dg.source a.
dg.source d.
```

`shortest` gives the least sum of weights; `dist` has a [bound column](../object/bound-columns.md).

```hugin,run
%use "std/graph".
city : type. a, b, c, d : city.
km : city -> city -> int -> rel.
km a b 5. km b c 3. km a c 10. km c d 1.
sp = shortest { node = city, edge = km }.
?- sp.dist a X D.
```

```output
?- sp.dist a X D.
X = b, D = 5.
X = c, D = 8.
X = d, D = 9.
```

`hops` counts the edges of the shortest walks.

```hugin,run
%use "std/graph".
city : type. a, b, c : city.
road : city -> city -> rel.
road a b. road b c. road a c.
h = hops { node = city, edge = road }.
%output h.dist.
```

```output
h.dist a b 1.
h.dist a c 1.
h.dist b c 1.
```

`bounded` gives the walks of at most `limit` edges, also in a graph with cycles, where their number of
edges is unbounded.

```hugin,run
%use "std/graph".
city : type. a, b : city.
road : city -> city -> rel.
road a b. road b a.
short = bounded { node = city, edge = road } 3.
%output short.hop.
```

```output
short.hop a a 2.
short.hop a b 1.
short.hop a b 3.
short.hop b a 1.
short.hop b a 3.
short.hop b b 2.
```
