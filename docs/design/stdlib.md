# A minimal standard library

Design note for [issue #61](https://github.com/k0uks1/hugin/issues/61): split the prelude into a small
auto-imported part and explicitly imported `std` modules, and decide their content. Status: proposal, for
review. Revision 2 replaces the `private` modifier by signature ascription (4.5, 4.6) after the
designer's review. Nothing is implemented. The spikes it cites were run against `9b82924` and are not
committed.

Contents: 1 recommendations, 2 prior art, 3 the prelude today, 4 structure, 5 content, 6 open questions,
7 startup time, 8 migration, 9 batches, 10 alternatives, 11 sources.

## 1. Recommendations

1. **Three layers, as in Lean's `Init.Prelude` / `Init` / `Std`.** The compiler-bound vocabulary moves to
   one file, `<stdlib>/std/reflect.hgn`. It holds everything the compiler looks up by name: `list`,
   `bool`, the reflective types, `quoted`, `decl` and its attributes, `modes`, the primitives and the
   primitive directives. It is loaded in every compilation, but its names are not in the user's scope.
   The prelude puts 21 names in scope: the base types, `bool`, `if`, `same`, `list`, `append`, `option`,
   and the directives `%input`, `%output`, `%open`, `%derivations`, `%terminates` and `%demand`.
   Everything else is in `std/` modules that a program imports.
2. **The compiler binds names by file, not by scope.** It looks up compiler-known names in the scope of
   `std/reflect` (today it looks in the prelude's scope, `file.parent`). A program can therefore declare
   `term`, `item`, `list` or `output` freely. Quotes, list syntax, mode items and directive footprints
   keep working, because they never see the program's names. No name is reserved apart from the keywords.
3. **Hiding is signature ascription, as in 1ML.** Signatures are record types, and transparent ascription
   `(e : S)` exists today: `(%import "lib2" : { double : int -> int })` hides `twice` (E0906, verified).
   The one addition for hiding is a place to write a file's own ascription: `%export S.` makes the file's
   module `(file : S)`. `std/demand` exports `{ demand : … }`, and its 27 helpers are hidden because the
   signature does not mention them. There is no modifier, no interface file and no new kind of
   declaration. Opaque sealing `(e :> S)` is designed in 4.6 but not proposed now, since no std module
   has an abstract type. Two other small additions serve the split, not hiding: `%use` opens a module's
   names (4.4), and import paths that start with `std/` denote the bundled library. The directive paths
   `%m.d` of the first version are dropped, because `%use` makes a module's directives available
   unqualified.
4. **`%demand` stays available without an import, but costs nothing unless it is used.** The prelude
   re-exports `demand` from `std/demand` *lazily*: the module is elaborated only in a compilation that
   resolves the name. This is unobservable, because `std/demand` declares no object constants. It removes
   the dominant prelude cost (section 7) without migrating the 30 programs that use `%demand`.
5. **Content follows the issue's minimality rule:**
   - `std/list` provides `map`, `filter`, `foldl`, `foldr`, `length`, `concat`, `reverse`, `zip`, `any`,
     `all`, `elem`, `diff`, `lookup`, the fuel type `nat` with `size` and `iterate`, and the object
     relations `len` and `member`;
   - `std/graph` provides graph transformers that compose (`reverse`, `undirected`), the closures `tc`
     and `rtc`, `reach`, `scc`, `degrees`, `shortest`, `hops` and `bounded`;
   - `std/order` provides `best` (argmin and argmax), `ranking`, `top` and `order`;
   - `std/directives` provides the binding analysis that `%demand` already contains, and traversals;
   - `std/demand` provides `%demand`.

   Every combinator in section 5 was compiled and run in a spike.
6. **Open questions.**
   - *`list` and `seq`*: #80 settled this. There is one shared `list`.
   - *Built-in `%demand` for `len`*: no. The call site's file writes `%demand len +l -n.`, which works
     for an imported `len` (verified).
   - *An object formula `true`*: no. `bool` becomes shared data, so `bool` columns exist at the object
     level (as in Rel, QL, Flix and Logica). A new lint reports a nullary constant used as a body atom,
     since such an atom always holds (`p :- false.` derives `p`).
7. **Startup time.** A spike of the trimmed prelude elaborates in 13 ms against 47 ms (warm, uncached,
   medians). In a cold JVM it takes 1.37 s against 2.16 s. A cold `hugin check` of a one-line program
   takes 2.0 s against 3.2 s on a loaded machine.
8. **Migration.** `%demand` programs do not change. 11 programs add `%use "std/graph".` and 9 add
   `%use "std/list".`. `pair` is deleted, and 2 reference examples declare it themselves. About 10
   goldens change: 5 show prelude line numbers, the rest have shifted lines, numbered unknowns or
   completion lists. `--no-prelude` keeps its meaning, and a program compiled with it can now
   `%import "std/reflect"`.
9. **Six batches.** Each batch carries its own reference changes (section 9).

## 2. Prior art

Each finding is read from source. The checkouts are shallow clones at the commits listed in section 11.
Rel's source is not public, so its documentation was read instead.

### Meta-level references

**Lean 4.**
- *What is imported.* A file imports `Init` unless its header has the token `prelude`
  (`src/Lean/Elab/Import.lean:29-33`, `HeaderSyntax.imports`). `Init` re-exports about 15 modules with
  `public import` (`src/Init.lean`).
- *How it is layered.* `Init.Prelude` (`src/Init/Prelude.lean`, 6 168 lines) is "the first file in the
  Lean import hierarchy", holding the "basic definitions, most of which Lean already has built in
  knowledge about". `Bool` (line 107), `Prod` (610), `Decidable` (1146), `Nat` (1357) and `List` (3116)
  are declared there with `@[extern]` implementations. List operations are layered: `List.foldl` and
  `List.append` are in `Init.Prelude`, while `filter`, `foldr`, `lookup` and `zip` are in
  `Init/Data/List/Basic.lean`. Collections that are not needed by the core (hash maps, tree maps, time,
  networking) are in `Std` (`src/Std.lean`, `src/Std/Data.lean`). `Std` is imported explicitly.
- *Names and shadowing.* Names are hierarchical (`List.map`), and there is one global environment. The
  elaborator refers to compiler-known constants by fully qualified, compile-time-checked names
  (``` ``List.cons ```, e.g. `src/Lean/Elab/Tactic/Do/Attr.lean:166`). A user namespace can reuse a short
  name without affecting them. `export ForIn (forIn)` re-exports a name into the current namespace
  (`src/Init/Core.lean:388`).
- *Lesson for Hugin.* Compiler-known names live in one fixed module, and are found there by the compiler,
  not through the user's scope. A small opt-out exists for bootstrapping (`prelude`).

**Idris 2.**
- *What is imported.* `libs/prelude/Prelude.idr` states the policy in its header: "The Prelude is minimal
  (since it is effectively part of the language specification ...). A rule of thumb is that it should
  contain the basic functions required by almost any non-trivial program." First on its list is "Anything
  the elaborator can desugar to (e.g. pairs, unit, =, laziness)", then `Bool`, `Nat`, `List`, `Dec`,
  `Maybe` and `Either`.
- *How it is layered.* The prelude is 4 319 lines in 14 files. `libs/base` has 136 files with what moved
  out: `Data.Vect`, `Data.Fin`, `Data.List.Elem`, `Decidable.Equality` (`DecEq`), `Data.SortedMap`.
- *How the compiler finds its names.* The prelude registers names with pragmas: `%pair Pair fst snd`
  (`Builtin.idr:75`), `%rewrite Equal rewrite__impl` (159), `%integerLit fromInteger`
  (`Prelude/Num.idr:12`).
- *Lesson for Hugin.* `fin`, `vec` and decidable equality as a class are in `base`, not in the prelude.
  The test for the prelude is "what the elaborator desugars to, plus what almost every program needs".

**Agda standard library.**
- *What is imported.* Agda has no implicit prelude. Every module imports what it uses.
- *How it is layered.* The `Base` modules hold definitions, and the `Properties` modules hold proofs:
  `src/Data/Nat.agda` re-exports `Data.Nat.Base` and `Data.Nat.Properties`. `Core` modules exist only to
  break import cycles (`Relation.Binary.PropositionalEquality.Core`). Builtins come from Agda itself:
  `open import Agda.Builtin.Nat public using (zero; suc) renaming (Nat to ℕ)`
  (`src/Data/Nat/Base.agda:28`).
- *Decidable equality.* `Dec` is a record with a boolean `does` and a `proof`, so that computing with it
  only needs the boolean (`src/Relation/Nullary/Decidable/Core.agda:52`). `DecidableEquality A` is
  `Decidable _≡_` (`src/Relation/Binary/Definitions.agda:276`).
- *Closures.* Closures are types: `TransClosure` (`Relation/Binary/Construct/Closure/Transitive.agda:31`)
  and `Star` (`.../ReflexiveTransitive.agda:21`). There are separate modules for `Symmetric`, `Reflexive`
  and `Equivalence`.
- *Lesson for Hugin.* There is one module per concept, and the boolean part of decidability is enough for
  computation. For meta code over atoms, `same : A -> A -> bool` is that boolean part.

**Haskell `base` and an alternative prelude.**
- *What `base` exports.* `libraries/base/src/Prelude.hs` (fetched from GHC `master`) exports the partial
  `head`, `tail` and `(!!)`, string I/O, `Read`/`Show`, the numeric tower and `seq`. This is the
  legacy-growth case: names that cannot be removed because every module imports them.
- *What relude changes.* relude (`src/Relude.hs`) replaces the prelude through Cabal `mixins`. It
  re-exports `head`, `tail`, `init` and `last` from `Data.List.NonEmpty`, so that they are total
  (`src/Relude/List/NonEmpty.hs:27`). Its `cycle` returns `[]` on `[]` instead of failing
  (`src/Relude/List/Reexport.hs`). Extras go into `Relude.Extra.*`, imported explicitly.
- *Lesson for Hugin.* The prelude is hard to shrink later, so it should start small. Hugin's meta level
  is total already, so there is nothing partial to remove.

### Object-level references

**Soufflé.**
- *Library.* Soufflé has no standard library. Reuse is by `.include` and the C preprocessor
  (`src/parser/scanner.ll:156`), by components `.comp` with type parameters, inheritance, `.init` and
  `.override` (`scanner.ll:148-152`; `tests/example/comp-parametrized/comp-parametrized.dl`), and by
  functors. A functor is an intrinsic such as `cat`, `strlen`, `substr`, `ord`, `range`, `to_number` or
  `min`, or a user-defined external function declared with `.functor` (`src/FunctorOps.cpp`).
- *Booleans.* There is no boolean type. The type attributes are `Symbol`, `Signed`, `Unsigned`, `Float`,
  `Record` and `ADT` (`src/include/souffle/TypeAttribute.h:28`). `true` and `false` are nullary
  constraints, that is, formulas (`src/parser/parser.yy:1023-1030`, `ast::BooleanConstraint`). `land`,
  `lor` and `lnot` work on numbers.
- *Closures.* Every program writes its closures by hand.

**Flix.**
- *Library.* The library modules are reached by qualified name (`List.map`) without an import
  (`examples/functional-style/function-composition-pipelines-and-currying.flix`). `Prelude.flix` puts a
  few combinators in the root namespace (`identity`, `flip`, `fst`, `snd`, `|>`).
- *Datalog.* Datalog programs are first-class values, typed by row-polymorphic schemas. `Graph.flix`
  writes each algorithm as a host function that builds and composes constraint sets.
  - `reachability(): #{ Edge(t, t), Reachable(t, t), Node(t) | r }` (`main/src/library/Graph.flix:513`)
    and `nodes()` are composed in `closure` with `query edges, nodes(), reachability()` (line 20).
  - Shortest distances use a lattice column: `Dist(x, y; d1 + Down.Down(d2)) :- Dist(x, z; d1), ...`
    (line 203).
  - The other operations are `degrees`, `inDegrees`, `outDegrees`, `stronglyConnectedComponents` (mutual
    reachability, line 69), `topologicalSort`, `isCyclic`, `withinEdgesOf` and `cutPoints`.
- *Booleans.* `Bool` is an ordinary term type, so `R(Bool)` is a relation. A nullary predicate serves as
  a proposition: `Cycle :- Path(x, x).` (`examples/datalog/is-cyclic.flix`).
- *Lesson for Hugin.* This is the closest analogue to Hugin's two levels. The graph library is a set of
  functions from inputs to rules, and the rules compose.

**CodeQL.**
- *Closures.* Closures are syntax: `p+(a, b)` and `p*(a, b)` on a predicate of relational arity 2
  (`docs/codeql/ql-language-reference/ql-language-specification.rst:517`, `recursion.rst:73`).
- *What is in scope.* The global namespaces hold the primitive types `int`, `float`, `string`, `boolean`
  and `date`, the built-in predicates and the module `QlBuiltins` (`name-resolution.rst:195-213`).
  `QlBuiltins::EquivalenceRelation<T, base/2>` is the symmetric-transitive closure as a parameterised
  module (`modules.rst:287`). Everything else is imported (`import java`).
- *Library modules.* They are parameterised by signature modules:
  `module DenseRank<DenseRankInputSig Input>` (`shared/util/codeql/util/DenseRank.qll`), and data flow is
  `module Global<ConfigSig Config>` (`shared/dataflow/codeql/dataflow/DataFlow.qll:1122`). A `ConfigSig`
  has `default predicate isBarrier(Node node) { none() }` (line 416): signatures carry defaults.
  `shared/util/codeql/util/` has 15 small modules (`Boolean`, `Option`, `Either`, `Unit`, `DenseRank`,
  `Strings`, ...).
- *Booleans.* `boolean` is a primitive type with values `true` and `false`
  (`ql-language-specification.rst:438`). The formulas are `any()` and `none()` (`formulas.rst:329`).
  `Boolean.qll` wraps `boolean` so that it "does not require explicit binding".
- *Lesson for Hugin.* A Hugin functor with a signature parameter is the same construct as a parameterised
  module, so the graph library should be functors over signatures.

**Logica.**
- *Library.* `lib/` holds three files. `lib/closure.l` computes `TransitiveClosure` by squaring a fixed
  number of times through functor substitution (`TC2 := TC1(TC0: TC1);` up to `TC4`), and `GraphDistance`
  with `Min=` (`lib/reachability.l`). Programs import them with `import lib.closure.TransitiveClosure;`
  (`examples/scripts/closure_use.l`).
- *What is in scope.* A per-dialect library is prepended to every program
  (`compiler/universe.py:637-640`). In SQLite it defines functions as predicates with a value column:
  `ArgMin(arr) = Element(SqlExpr("ArgMin({a}, {v}, 1)", ...), 0) :- Arrow(a, v) == arr;`, `ArgMaxK`,
  `ReadFile` (`compiler/dialect_libraries/sqlite_library.py`).
- *Booleans.* `true` and `false` are literal values (`parser_py/parse.py:577`).
- *Lesson for Hugin.* argmin, argmax and top-k are what users reach for. Recursion bounded by unrolling
  is a workaround that Hugin's termination check makes unnecessary.

**Rel (RelationalAI).**
- *Library.* The library list has three groups: Core (`stdlib`, `intrinsics`, `mirror`), Math and
  Computer Science (`alglib`, `histogram`), and Visualisation (rel.relational.ai/rel/ref/lib). `stdlib`
  defines `argmax`, `argmin`, `top`, `bottom`, `sort`, `enumerate` and `arity`, "a higher-order relation
  that is always evaluated at compile-time" (rel/ref/lib/stdlib).
- *Booleans.* "The relation `true` is represented by an empty tuple `()`, which is a relation of arity 0
  and cardinality 1. The relation `false` is the empty relation `{}`." Separately, a `Boolean` data type
  with constructors `boolean_true` and `boolean_false` is "useful for importing data"
  (rel/ref/data-types/other).
- *Lesson for Hugin.* Logical truth is a nullary relation, and a boolean *value* type exists for data.

**SWI-Prolog.**
- *Vocabulary.*
  - `library(lists)` has `member`, `append`, `nth0`, `nth1`, `last`, `reverse`, `sum_list`, `max_list`,
    `numlist`, `list_to_set`, `subtract`, `max_member/3` (`library/lists.pl`).
  - `library(apply)` has `include`, `exclude`, `partition`, `maplist/2..5`, `foldl/4..7` and `scanl`
    (`library/apply.pl`).
  - `library(aggregate)` has `aggregate_all/3` with `max(Expr, Witness)` and `min(Expr, Witness)`, which
    are argmax and argmin (`library/aggregate.pl:117-125`).
- *What is in scope.* Library predicates are autoloaded when a call finds no definition:
  `'$undefined_procedure'` calls `'$autoload'` only after the predicate is found undefined
  (`boot/init.pl:946-956`), so a local definition always takes precedence.

### Module systems

Hugin's modules are dependent records: a module body or a file is a record value, a signature is a record
type, a functor is a meta function. 1ML is the closest design, and MixML, Agda and Lean bear on parts of
it. SML and OCaml supply the vocabulary.

**1ML** (Rossberg, JFP 2018; `rossberg/1ml`).
- *One language.* "ML is two languages in one: there is the core [...] and there are modules [...].
  Modules form a separate, higher-order functional language on top of the core" (abstract). 1ML removes
  the second language: `type` is a type of small types, `{ D }` is both a record type and a signature,
  and `(X : T) -> E` is both a function type and a functor type (`README.txt`, kernel syntax).
- *Ascription.* There are two forms, as in SML: "opaquely (E :> T), which performs sealing [...], that
  is, any type that is specified abstractly in T will be opaque", and "transparently (E : T), which
  implicitly refines all abstract specifications in T with their actual definitions from E". The
  transparent form "can simply be encoded as applying the identity functor at type T" (section 2,
  "Transparent vs. Opaque Type Ascription"). Sealing elaborates to existential packing,
  `E :> T ~> unwrap (wrap E : T) : T` (`README.txt`, derived syntax).
- *Translucency.* A type field is either abstract (`size : type`) or manifest through a singleton
  (`size : (= type int)`, written `type size = int` in a signature), and `T with .X = E` refines a field
  (section 2, "Translucency"). Sharing is expressed by singletons and dependency, with no separate
  construct.
- *Practice.* `prelude.1ml` seals each library value: `List :> LIST = { … }` (line 163),
  `Set (Elem : ORD) :> SET with (elem = Elem.t) = …` (line 215). Helpers are hidden by `local … in`,
  which is `include (let B1 in {B2})`: lexical scope, not a modifier.
- *Lesson for Hugin.* Hugin already has 1ML's shape: record types as signatures, ascription as an
  expression, functors as functions, sharing by dependent field types. What it lacks is a place for a
  file to ascribe itself (1ML has no files), and sealing.

**MixML** (Rossberg and Dreyer, TOPLAS 2013). "A MixML module is like an ML structure in which some of
the components are specified but not defined. In other words, it unifies the ML structure and signature
languages into one" (abstract). Its purpose is recursive linking of separately compiled components
(`new UA with new UB` links two units that import each other's components, p. 16). It bears on Hugin in
one respect only: Hugin's import graph is acyclic by design (E0108), files are elaborated once per
compilation in dependency order, and there is no separate compilation, so mixin linking has nothing to
solve. Hugin keeps signatures as types, as 1ML does, and does not merge them with modules, as MixML does.

**Agda.** Records serve as signatures, and abstraction is a property of a definition.
`Data/List/Sort.agda` (lines 31-42) seals a choice of algorithm:
`abstract sortingAlgorithm : SortingAlgorithm; sortingAlgorithm = mergeSort` makes the value opaque
outside the `abstract` block, and
`open SortingAlgorithm sortingAlgorithm public using (sort; sort-↭; sort-↗)` re-exports a selection of
its fields. `SortingAlgorithm` is a record type with a function and its correctness properties
(`Data/List/Sort/Base.agda:28`). This is 1ML's sealing without existentials: an opaque definition of a
record-typed value.

**Lean 4.** Structures are records, and there are no module signatures. Abstraction is per definition:
`opaque Quot` and `opaque Quot.mk` (`src/Init/Prelude.lean:439-446`) cannot be unfolded by the type
checker but are compiled and run. Hiding is `private` (line 1970). Lean has neither ascription of a
module nor sealing.

**SML and OCaml** (vocabulary only).
- SML: HaMLet (`rossberg/hamlet`), an implementation of the Definition, has transparent ascription (Rule
  52: the matched structure keeps its types) and opaque ascription (Rule 53: the result has the
  signature's fresh type names), `where type` (Rule 64), `include` (Rule 75) and sharing (Rules 78-79),
  in `elab/ElabModule.sml`.
- OCaml: a compilation unit behaves "roughly as the module definition
  `module U : sig I end = struct M end`" (`manual/src/refman/compunit.etex`). The interface hides what it
  does not list: `stdlib/list.ml` defines `length_aux`, which `stdlib/list.mli` does not mention.
  `map.mli` has the functor `module Make (Ord : OrderedType) : S with type key = Ord.t` (line 377).
  Destructive substitution `with type t := …` removes a type from a signature
  (`extensions/signaturesubstitution.etex`), and `module type of` is deliberately not strengthened
  (`extensions/moduletypeof.etex`). OCaml's single ascription `:` seals the types a signature leaves
  abstract (1ML, footnote 8).

### Summary

| | prelude or implicit scope | other library | how the compiler finds builtins | closures | object boolean |
|---|---|---|---|---|---|
| Lean 4 | `Init` (opt out: `prelude`) | `Std`, imported | fully qualified constants in `Init.Prelude` | library | `Bool` |
| Idris 2 | `Prelude`, minimal by policy | `base`, imported | pragmas in the prelude (`%pair`, `%integerLit`) | library | `Bool` |
| Agda | none | all imported | `BUILTIN` pragmas in `Agda.Builtin.*` | `Star`, `TransClosure` types | `Bool` |
| Soufflé | none | `.include`, components | fixed in the grammar | by hand | none; `true`/`false` are constraints |
| Flix | `Prelude.flix`; modules by qualified name | everything qualified | language | host functions returning rules | `Bool` term type |
| CodeQL | primitive types, builtins, `QlBuiltins` | imported | language | `+`, `*`; `EquivalenceRelation` | `boolean`; `any()`, `none()` |
| Logica | dialect library prepended | `lib/`, imported | SQL templates | unrolled squaring | literals |
| Rel | stdlib | named libraries | intrinsics | library | `true`/`false` relations; `Boolean` data |
| SWI-Prolog | autoload on undefined call | `library(...)` | system module | library | atoms |

## 3. The prelude today

`src/main/resources/hugin/stdlib/prelude.hgn` (466 lines) declares 144 names. The numbers below count
files that use a name. They were counted by a word search that skipped comments and files declaring the
name themselves, and checked by hand for the names that move. The groups are:
- *tests*: `tests/**/*.hgn`;
- *ex.*: `examples`, `docs/design/examples` and `bench`;
- *ref.*: `reference/src` and `docs/errors`.

*Compiler* names the place where the compiler looks the name up:
- `RG` is `ReflectiveGlobals` (`core/elab/Reflective.scala`, 59 names);
- `TQ` is `TypedQuotes.typed` and `QuotedPatterns.typedGlobal`;
- `MD` is `Directives.modeData`;
- `PR` is `Primitives` with `x : A = %builtin p.`;
- `DA` is `DeclAttributes`.

The verdicts are:
- *reflect* (in `std/reflect`, not in the user's scope);
- *reflect, opened* (in `std/reflect`, put in scope by the prelude);
- *prelude* (declared by the prelude);
- *std/X* (moved to that module);
- *std/X, outside its signature* (moved; not in the module's `%export` signature);
- *delete*.

| declarations | tests | ex. | ref. | compiler | verdict |
|---|---:|---:|---:|---|---|
| `list`, `nil`, `cons` | 39 | 4 | 20 | RG, list syntax, `DA` | reflect, opened |
| `len` | 6 | 3 | 3 | none | std/list |
| `option`, `none`, `some` | 9 | 2 | 10 | none | prelude |
| `pair` | 0 | 0 | 2 | none | delete (a one-line struct; record types serve the meta level) |
| `graph`, `tc`, `bounded` | 10 | 3 | 5 | none | std/graph |
| `append` | 2 | 0 | 1 | RG (splices `$..`) | reflect, opened |
| `sym`, `index`, `izero`, `isuc` | 2 | 0 | 2 | RG | reflect |
| `arith_op` and its 5 constructors | 0 | 0 | 2 | RG | reflect |
| `cmp_op` and its 6 constructors | 0 | 0 | 2 | RG | reflect |
| `agg_op` and its 4 constructors | 0 | 0 | 2 | RG | reflect |
| `term` and its 9 constructors | 5 | 0 | 3 | RG | reflect |
| `quoted`, `qterm`, `raw` | 9 | 1 | 7 | TQ | reflect |
| `formula` and its 6 constructors | 2 | 0 | 2 | RG | reflect |
| `rule`, `horn`, `column`, `colof`, `module` | 3 | 0 | 4 | RG | reflect |
| `item` and its 5 constructors | 2 | 0 | 3 | RG | reflect |
| `openT`, `openF` | 0 | 0 | 1 | RG (higher-order holes) | reflect |
| `pick`, `openTs` | 0 | 0 | 1 | none | reflect (`pick` becomes local to `openT` by `where`) |
| `measure`, `mvars`, `mlabels` | 3 | 0 | 2 | RG, DA | reflect |
| `attr` and its 5 constructors | 0 | 0 | 2 | RG, DA | reflect |
| `decl`, `dconst`, `drule`, `derror` | 2 | 0 | 3 | RG, DA | reflect |
| `attach` | 0 | 0 | 1 | none | reflect |
| `input`, `output`, `open`, `derivations`, `terminates` | most | most | many | directive resolution | reflect, opened |
| `bool`, `true`, `false` | 0 | 2 | 3 | PR (result constructors) | reflect, opened; shared data (6.3) |
| `same` | 2 | 2 | 1 | PR | reflect, opened |
| `labels`, `derive`, `derived` | 1 | 0 | 3 | PR | reflect |
| `modes`, `mnone`, `minput`, `moutput` | 0 | 0 | 2 | MD | reflect |
| `demand` | 27 | 3 | 8 | none | std/demand, lazily re-exported by the prelude |
| 27 helpers `ddemanded` … `dothers` (all `d…` except those below) | 0 | 0 | 1 | none | std/demand, outside its signature |
| `tvarsOf`, `tsvars`, `fvars`, `fbound`, `fneeds`, `dequation`, `plain`, `plains` | 0 | 0 | 1 | none | std/directives |
| `band`, `bor`, `member`, `sdiff`, `shares`, `msym`, `dkeepS`, `dunless`, `ditems` | 0 | 2 | 1 | none | delete (replaced by `if` and `std/list`) |

Some counts include unrelated uses of a common word. `same` matches comments in 20 tests, `term` and
`rule` match English, and `member` matches module members. The `member` and `plain` hits in tests are the
programs' own names, and none of the tests' hits for `band`, `bor`, `sdiff` or `shares` is the prelude's.
The two uses of `band` and `bor` are in `docs/design/examples`.

Verdict counts over the 144 names:

| verdict | names |
|---|---:|
| `std/reflect`, not in the user's scope | 78 |
| `std/reflect`, opened by the prelude | 13 |
| declared by the prelude | 3 |
| `std/demand` (1 in its signature, 27 outside) | 28 |
| `std/directives` | 8 |
| `std/list` | 1 |
| `std/graph` | 3 |
| deleted | 10 |

In scope in every file: 144 names today, 21 after the change. They are the 13 opened names, the 3 of
`option`, `if` (new, in `std/reflect`), `demand`, and the base types `int`, `float` and `string`.

## 4. Structure

### 4.1 Files and scopes

```text
<stdlib>/std/reflect.hgn   compiler-bound; sees nothing (base types by %builtin); loaded first
<stdlib>/prelude.hgn       %use of std/reflect (13 names); option; lazy %use of std/demand (demand)
<stdlib>/std/demand.hgn    %export { demand : … }; imports std/directives and std/list
<stdlib>/std/directives.hgn binding analysis, traversals, fresh names, errors
<stdlib>/std/list.hgn      meta list functions, nat and iterate, object len and member
<stdlib>/std/graph.hgn     graph signatures and functors
<stdlib>/std/order.hgn     argmin and argmax, ranking, top-k, order on finite sets
```

```text
std/reflect   (not in any user scope; found by the compiler by file)
prelude       (encloses every file)
├── program
├── std/list, std/graph, … (imported files see the prelude, as today)
└── lib/*.hgn
```

`std/reflect` plays the role of Lean's `Init.Prelude`: it is elaborated with no enclosing scope and holds
what the compiler desugars to. The prelude plays the role of `Init`: it is small and re-exports.
`std/graph` and the others play the role of `Std`.

### 4.2 How the compiler finds its names

`ReflectiveGlobals`, `TypedQuotes.typed`, `QuotedPatterns.typedGlobal`, `Directives.modeData` and the
result constructors of `Primitives` look up names in the scope of the file `<stdlib>/std/reflect.hgn`, by
name, once per compilation. A missing name is an internal error at load, not E0917. The fallback for
compilations without that file stays: the names are looked up in the root file, which is how
`ReflectionSuite` bootstraps (it concatenates the prelude's text into a program compiled without it).

Consequences:
- A program's `term`, `item`, `list`, `quoted` or `modes` never changes what quotes, list syntax, typed
  holes or mode items build. This is already true for the program's own declarations today (reference:
  reflection, "The compiler finds the reflective types in the prelude's scope"). After the change it also
  holds for names that a program opens with `%use`.
- `--no-prelude` loads neither the prelude nor `std/reflect`. A program compiled with it may write
  `%import "std/reflect"` or `%use "std/reflect".` and then quote. Today it cannot import the reflective
  types at all, and E0917 says so.

### 4.3 Reserved and shadowable names

No name is reserved apart from the keywords of `reference/src/lexical-structure.md`. Every prelude name
may be shadowed, with the rule that holds today: a declaration shadows the same name of an enclosing
scope in the whole scope, and the shadowed object constant is displayed as `prelude.n`.

Shadowing a compiler-known name cannot break the compiler, by 4.2. What shadowing does take away is the
name: a program that declares its own `output` cannot write `%output` (E1001, as today). It can still
write `%use "std/reflect" (output)` under another name if `%use` gets renaming. Renaming is not proposed,
since no test or example needs it.

> **Rationale.** Lean forbids redeclaring a root name and has namespaces instead. Hugin has no
> namespaces, only nested scopes, so shadowing is the mechanism that exists. The defect that the issue
> names ("users cannot declare their own `term` or `item` without shadowing") is that the names are in
> scope at all. After the change they are not.

### 4.4 `%use`

```text
Use ::= "%use" (STRING | Path) ("(" NAME ("," NAME)* ")")? "."
```

- `%use "std/graph".` imports the file (as `%import` does) and opens its public names. `%use m.` opens
  the module `m`, which may be an import or a module value.
- With a list of names, only those are opened. It is an error if one is not a member.
- Opened names form a scope between the file's own declarations and the enclosing scope. The file's
  declarations shadow them, and they shadow the prelude.
- Two opened names that denote the same entity are the same name, so `%use "std/reflect" (list)` next to
  the prelude's `list` is not a clash. Two that denote different entities make the name ambiguous: a use
  is an error (new code E0109), and a declaration of the file resolves it.
- Names opened in the prelude are visible in every file, because the prelude's scope encloses them. This
  is how the prelude re-exports from `std/reflect`, like Lean's `export`.

`%use` opens the fields of the module's *type*, so it follows signatures. `%use "std/demand".` opens
`demand` only, since that is the signature `std/demand` exports (4.5). `%use (%import "f" : S).` opens
the fields of `S`. A name in the list must be a field of the type (E0906 otherwise). An opened name
stands for the projection `m.x`: under transparent ascription the projection reduces to the entity, so an
opened constructor is still a constructor in patterns, and two opens of the same entity agree.

`%use` is a scope form handled by the elaborator, like `%import`. It is not a directive (a meta
function), since a directive cannot change scopes. It is the one addition that the split needs beyond
hiding: neither ascription nor import can bring names into scope unqualified.

> **Note.** `%open` is taken: it declares a relation incomplete (reference: object/negation). So the form
> is called `%use`.

### 4.5 Signatures and hiding

What signatures express today, checked against the implementation (`core/elab/Records.scala`,
`core/elab/Imports.scala`) and by spikes:

| ML feature | Hugin today | decision |
|---|---|---|
| signature | a record type `{ … }`, a telescope with `%complete` requirements (`checkRecordType`) | have |
| structure | a module body, a file, a record value | have |
| functor | a meta function with a signature-typed parameter; the parameter's types are abstract in the body (#56) | have |
| first-class module | records are values | have |
| transparent ascription `:` | `x : S = e.` and the expression `(e : S)`; fields not in `S` are hidden (E0906); the types stay transparent because the ascribed definition unfolds (`g : graph = { node = city, … }` then `g.edge a X` type-checks) | have |
| sharing constraints | dependent parameter types: `both (g : graph) (h : { edge : g.node -> g.node -> rel })` ran | have, by dependency |
| file interface (`.mli`) | only at the importer: `s : S = %import "f"` | **adopt as `%export S.`**, the one addition |
| opaque ascription `:>` | none (`docs/LIBRARIES.md`, "Sealing": not done) | **designed below, not proposed now** |
| manifest specifications, `where type`, singletons `(= E)` | none: `{ node : type = city }` is E0001 | reject now; only sealing needs them |
| `include` in signatures | none | reject: `complete_graph` is one line, and record subtyping makes a complete graph a `graph` |
| destructive substitution `:=`, `module type of` | none | reject: no signature in the stdlib is built from another |
| recursive modules, mixin linking (MixML) | acyclic imports (E0108) | reject |
| `open` (Agda `open … public using`) | none | adopt as `%use` (4.4), for the split, not for hiding |

**Why the existing language cannot express a file's interface.** A file is a record whose value is bound
by its importers, so the only ascription that exists is at the import site. That puts the signature in
every importer. The prelude could write
`%use (%import "std/demand" : { demand : (r : sym) -> modes (labels r) -> module -> module }).`, but a
program that imports `std/demand` itself would still see the 27 helpers. 1ML's way, a sealed record
inside the file (`lib : S = { … }.`), is blocked: meta functions by clauses are E0907 in a module body
(spiked), and the file would export `lib` as well.

**`%export S.`** ascribes the file's own module value, exactly as `(file : S)` would:

```hugin,ignore
(* std/demand.hgn, today: every declaration is a field of the import *)
demand : (r : sym) -> modes (labels r) -> module -> module.
demand R M Is = irelation (derive R "check") (dcolumns R izero M) :: dmodule R … .
dmodule : sym -> list sym -> modes Ls -> list formula -> module -> module.
…                                                   (* 26 more helpers *)

(* after: one item states what the file exports *)
%export { demand : (r : sym) -> modes (labels r) -> module -> module }.
demand : (r : sym) -> modes (labels r) -> module -> module.
…
```

```hugin,ignore
d = %import "std/demand".
x = d.dmodule.          (* error[E0906]: no field `dmodule`; `{ demand : … }` has the field `demand` *)
%use "std/demand".      (* opens `demand` only *)
```

The rules:
- `S` is elaborated in the file's scope after its declarations, so it may mention them.
- It is an error ([E0204](../errors/E0204.md)) if the file's module does not match `S`, with the note
  that the mismatch is against the file's `%export`.
- It is an error (new code E0110) to write `%export` twice or inside a module body.
- A file without `%export` exports all its declarations, as today.

Ascription is transparent, so nothing changes for what is exported: a type stays its definition, a
constructor field stays a constructor (in patterns and in object code), and a relation is the same
relation. What is hidden still exists: a relation that the signature leaves out is evaluated, its facts
keep their identity, and `--all-relations` prints them under its own name. Hiding is static and concerns
names only, as ascription does in SML's dynamic semantics.

**Which std modules export a signature.** Only `std/demand` hides anything. `std/reflect` moves `pick`
into a `where` block of the `openT` clause that uses it, which hides it lexically, as 1ML's `local` does.
`openTs` stays a field: it is mutually recursive with `openT`, and `where` blocks have no forward
references. `std/list`, `std/graph`, `std/order` and `std/directives` export everything, and their
reference pages list their fields.

**Named signatures.** `std/graph` exports the signatures `graph`, `complete_graph` and `weighted`, and
`std/order` exports `scores` and `ints`. They are `Type` definitions, so they are values of the module
like its functors, and they are the parameter types of the functors. The export signature of `std/demand`
is not named: no program ascribes to it.

### 4.6 Opaque ascription (designed, not proposed now)

Sealing is the addition that 1ML treats as primitive. Hugin needs it only for an abstract type, such as a
set whose representation is hidden. No std module in section 5 has one, so it is not proposed, but it
fits as follows:

```hugin,ignore
(* today: s.shape is the file's shape, and its constants are visible *)
shapes_sig : Type = { shape : type, square : int -> shape, area : shape -> int -> rel }.
s : shapes_sig = %import "lib/shapes".
(* sealed: s.shape is abstract; s.square 3 is a value of s.shape, and nothing else is *)
s :> shapes_sig = %import "lib/shapes".
```

- `x :> S = e.` and `(e :> S)` check `e` against `S` like `:`, and the definition does not unfold in
  conversion. This is Agda's `abstract` and Lean's `opaque`, not 1ML's existential packing: Hugin has no
  impredicative `wrap`, and an opaque definition gives its users the same view.
- A type field of `S` is then an abstract object type, one per sealed definition: #56's abstract heads of
  functor parameters, compatible only with themselves. One rule differs: an operand check on a sealed
  type (a comparison, arithmetic, a literal) is an error, where a functor body defers it to the
  instances.
- Staging and directives evaluate through the seal. The object program uses the real constants, so facts
  keep their identity and print under their names. A constructor that `S` leaves out cannot be named, so
  importers can neither build nor match its facts: an abstract data type of facts.
- Sealing needs manifest fields to say what stays visible (`S where node = city`, 1ML's `T with .X = E`).
  That is the second half of the same addition. It is not needed while ascription stays transparent.

### 4.7 `std/` paths

An import path that starts with `std/` denotes `<stdlib>/std/…` and is not resolved relative to the
importing file. A local directory named `std` is imported as `./std/x`. This is the reserved crate prefix
of Rust's `std::`.

### 4.8 Lazy re-export

`%use "std/demand" (demand).` in the prelude is *lazy*: `std/demand` is parsed with the prelude (its
imports belong to the import graph, which stays static), but it is elaborated only when a name it
provides is resolved.

Laziness is allowed only for a file that declares no object constants. Its evaluation creates nothing, so
whether it ran cannot be observed. The compiler checks this condition and elaborates the file eagerly if
it does not hold.

`ElabLibrary` is already a query, so the language server and the REPL elaborate `std/demand` at most once
per revision, and `StdlibCache` once per process.

## 5. Content

Every block in this section was compiled and run against `9b82924`. The `std/` files were imported
relatively, with aliases in place of `%use`. They are in the session's scratchpad
(`spike/final/std/*.hgn`) and are not committed. The names follow the module (`l.map` after
`l = %import "std/list".`). With `%use` they are plain (`map`).

### 5.1 The prelude

```hugin,ignore
%use "std/reflect" (bool, true, false, if, same, list, nil, cons, append,
                    input, output, open, derivations, terminates).
%use "std/demand" (demand).        (* lazy, 4.8 *)

option A : data.
none : option A.
some : A -> option A.
```

`if : bool -> A -> A -> A` is new and lives next to `bool` in `std/reflect`. It replaces the two-clause
selector functions that the prelude defines today (`dkeepIf`, `dkeepS`, `dunless`, `dguardSel`, and
`addIf` and `stepEdge` in `docs/design/examples/graphs.hgn`). Evaluation is strict, so both branches are
evaluated. Meta applications are memoised, so `dedup` written with `if` stays linear; a spike over 30
elements ran in the time of a one-line program. A list literal after `if` must be in parentheses, since
`[B] []` reads as a lambda: `if c ([B]) []`.

### 5.2 `std/reflect`

`std/reflect` holds today's declarations of the reflective types, `decl`, `attr`, `measure`, `modes`, the
primitives and the primitive directives, unchanged, plus `if`. It also declares `bool` as `bool : data.`
(6.3). Nothing else is added. Reflection gets its own reference chapter today; after the change,
`reference/src/reflection.md` says "`std/reflect` declares" where it now says "the prelude declares".

### 5.3 `std/list`

The meta part:

```hugin,ignore
map     : (A -> B) -> list A -> list B
filter  : (A -> bool) -> list A -> list A
foldr   : (A -> B -> B) -> B -> list A -> B
foldl   : (B -> A -> B) -> B -> list A -> B
length  : list A -> int
concat  : list (list A) -> list A
reverse : list A -> list A
zip     : list A -> list B -> list { fst : A, snd : B }
any, all : (A -> bool) -> list A -> bool
elem    : A -> list A -> bool               (by same: atoms only)
diff    : list A -> list A -> list A        (by same)
lookup  : K -> list { key : K, value : V } -> option V
nat : Type. zero : nat. suc : nat -> nat.
size    : list A -> nat
iterate : nat -> (A -> A) -> A -> A
```

Pairs are record types (`{ fst : A, snd : B }`), which the meta level has already. There is no `pair`
family. The definitions are one clause per constructor. Two examples, with `if` from 5.1:

```hugin,ignore
filter P (X :: Xs) = if (P X) (X :: filter P Xs) (filter P Xs).
lookup K (E :: Es) = if (same K E.key) (some E.value) (lookup K Es).
```

The following program ran with the expected output:

```hugin,ignore
l = %import "std/list".
xs : list int = [3, 1, 2, 3].
r1 : list int -> rel.
r1 (l.map ([x] x * 10) xs).                         (* r1 [30, 10, 20, 30] *)
r4 : list int -> rel.
r4 (l.diff (l.concat [xs, l.reverse xs]) [3]).      (* r4 [1, 2, 2, 1] *)
r5 : option string -> rel.
r5 (l.lookup 2 [{ key = 1, value = "one" }, { key = 2, value = "two" }]).   (* r5 (some "two") *)
r6 : int -> rel.
r6 (l.length (l.zip xs ["a", "b"])).                (* r6 2 *)
```

`nat`, `size` and `iterate` are the fuel pattern that every meta fixed point needs, because a meta
function must be structurally recursive. `docs/design/examples/graphs.hgn` defines `nat`, `size`, `iter`,
`mem`, `addNew` and `addIf` for its meta reachability (36 lines). With `std/list` it becomes:

```hugin,ignore
step : list edge -> list int -> list int.
step G R = l.foldl ([acc] [x] l.if (l.elem x acc) acc (x :: acc)) R (l.concat (l.map (targets R) G)).
targets : list int -> edge -> list int.
targets R (e A B) = l.if (l.elem A R) ([B]) [].
reach : list edge -> int -> list int.
reach G X = l.iterate (l.size G) (step G) (step G [X]).      (* static_reach 3, as before *)
```

The object part covers the lists that are facts:

```hugin,ignore
len : (l : list A) -> (n : int) -> rel.
len nil 0.
len (cons X L) M :- cons X L, len L N, M = N + 1.

member : (l : list A) -> (x : A) -> rel.
member (cons X L) X :- cons X L.
member (cons X L) Y :- cons X L, member L Y.
```

`?- basket L, l.len L N, l.member L 4.` answered `L = cons 3 (cons 4 (cons 5 nil)), N = 3.` Both are
two-liners by line count, but they are not obvious: the guard `cons X L` is what makes guarded induction
apply, and the same rule without it is E0501, since nothing binds `X` (checked). That earns them their
place. Sums over list facts are left out, since `sum` is a keyword and the aggregate covers sums over
relations.

Not included:
- `fin` and `vec`: no directive needs them, and `modes (labels r)` already indexes modes by a list.
- A decidable-equality family: `same` is the decidable equality that directives need, on symbols, strings
  and numbers. Equality on constructed values is a clause function per type, as Agda's `does` part is.
- `head`, `nth` and `last`: they would return `option`, and no program in the repository needs them.

### 5.4 `std/graph`

The signatures:

```hugin,ignore
graph : Type = { node : type, edge : node -> node -> rel }.
complete_graph : Type = { node : type, edge : node -> node -> rel, %complete edge }.
weighted : Type = { node : type, edge : node -> node -> int -> rel }.
```

The general combinator is a functor from graphs to graphs. A transformer returns a module with `node` and
`edge`, so its result matches `graph` and composes with every other functor. This is Flix's "functions
returning rules" at the meta level, typed by signatures, as CodeQL's parameterised modules are.

```hugin,ignore
reverse (g : graph) = {
  node : type = g.node.
  edge : node -> node -> rel.
  edge Y X :- g.edge X Y.
}.
undirected (g : graph) = {             (* the symmetric closure *)
  node : type = g.node.
  edge : node -> node -> rel.
  edge X Y :- g.edge X Y.
  edge Y X :- g.edge X Y.
}.
vertices (g : graph) = { vertex : g.node -> rel.  vertex X :- g.edge X _.  vertex Y :- g.edge _ Y. }.
tc (g : graph) = {                     (* today's prelude tc *)
  path : g.node -> g.node -> rel.
  path X Y :- g.edge X Y.
  path X Z :- g.edge X Y, path Y Z.
}.
rtc (g : graph) = {
  v = vertices g.
  t = tc g.
  path : g.node -> g.node -> rel.
  path X X :- v.vertex X.
  path X Y :- t.path X Y.
}.
reach (g : graph) (seed : g.node -> rel) = {
  reached : g.node -> rel.
  reached X :- seed X.
  reached Y :- reached X, g.edge X Y.
}.
scc (g : graph) = {                    (* mutual reachability, as Flix's stronglyConnectedComponents *)
  r = rtc g.
  same : g.node -> g.node -> rel.
  same X Y :- r.path X Y, r.path Y X.
}.
degrees (g : complete_graph) = {       (* source, sink, out_degree, in_degree *)
  v = vertices g.
  source : g.node -> rel.      source X :- v.vertex X, not g.edge _ X.
  sink : g.node -> rel.        sink X :- v.vertex X, not g.edge X _.
  out_degree : g.node -> int -> rel.
  out_degree X N :- v.vertex X, N = count { Y | g.edge X Y }.
  in_degree : g.node -> int -> rel.
  in_degree X N :- v.vertex X, N = count { Y | g.edge Y X }.
}.
shortest (g : weighted) = {
  dist : g.node -> g.node -> (d : min int) -> rel.
  dist X Y D :- g.edge X Y D.
  dist X Z D :- dist X Y D1, g.edge Y Z W, D = D1 + W.
}.
hops (g : graph) = {                   (* unweighted shortest distance *)
  dist : g.node -> g.node -> (d : min int) -> rel.
  dist X Y 1 :- g.edge X Y.
  dist X Z D :- dist X Y D1, g.edge Y Z, D = D1 + 1.
}.
```

`bounded` stays as it is today. The spike wrote the bodies of `vertices`, `source` and `sink` on several
lines; they are joined above for space.

The following program ran on the graph `a→b, b→c, c→b, d→c`, with weights `a→b 5, b→c 3, a→c 10, c→d 1`:

```hugin,ignore
gr = %import "std/graph".
g = { node = city, edge = road }.
weak = gr.rtc (gr.undirected g).     (* weakly connected components: ?- weak.path a X gives a, b, c, d *)
back = gr.tc (gr.reverse g).         (* the predecessors: back.path c d, c a, c b, c c, … *)
fromA = gr.reach g start.            (* reached a, b, c *)
s = gr.scc g.                        (* same b c, same c b, and every node with itself *)
dg = gr.degrees g.                   (* source a, source d; in_degree b 2 *)
sp = gr.shortest { node = city, edge = km }.   (* dist a c 8, dist a d 9 *)
```

The equivalence closure is `rtc (undirected g)`, CodeQL's `EquivalenceRelation`. Weak components are the
same closure, and strong components are `scc`. None of them needs its own definition.

> **Note.** In the spike, `back = gr.tc (gr.reverse g).` named its relation `back#2.path`. The inner
> instance took the name of the definition, and the outer one got a suffix. Composed functors need a
> naming rule: the outer application should take the definition's name, and inner instances `_m1`. This
> belongs to batch B5.

Not included:
- Topological order: it needs a ranking over nodes, which `std/order` gives for `int` nodes only.
- Cut points.
- Directive forms of the closures (`%tc edge path`). They were spiked and work, but they repeat the
  functors.
- A demand-driven `tc`. A functor body cannot hold `%demand` (E0907), and `reach` covers the
  source-restricted case.

### 5.5 `std/order`

```hugin,ignore
scores : Type = { key : type, item : type, score : key -> item -> int -> rel, %complete score }.

best (s : scores) = {
  argmin : s.key -> s.item -> rel.
  argmin K X :- s.score K X V, V = min { W | s.score K _ W }.
  argmax : s.key -> s.item -> rel.
  argmax K X :- s.score K X V, V = max { W | s.score K _ W }.
}.
ranking (s : scores) = {             (* 1 + the number of better items; ties share a rank *)
  rank : s.key -> s.item -> int -> rel.
  rank K X R :- s.score K X V, C = count { Y | s.score K Y W, W > V }, R = C + 1.
}.
top (s : scores) (n : int) = {
  r = ranking s.
  top : s.key -> s.item -> rel.
  top K X :- r.rank K X R, R <= n.
}.

ints : Type = { elem : int -> rel, %complete elem }.
order (d : ints) = {                 (* first, next, position *)
  next : int -> int -> rel.
  next X Y :- d.elem X, Y = min { Z | d.elem Z, Z > X }.
  first : int -> rel.
  first X :- X = min { Z | d.elem Z }.
  position : int -> int -> rel.
  position X N :- d.elem X, N = count { Y | d.elem Y, Y < X }.
}.
```

The spike ran it on `points red ann 7, red bob 9, red cid 9, blue dan 3` and on `day 3, 10, 7`. It gave
`argmax red bob`, `argmax red cid`, `argmin red ann`, `rank red ann 3` and `top red bob`, `top red cid`,
`top blue dan`, then `first 3`, `next 3 7`, `next 7 10` and `position 10 2`. Top-k terminates because the
ranking is a non-recursive aggregate over a complete relation. Ties are kept, so `top s 1` may hold
several items, as SQL's `RANK` does. `R = count { … } + 1` is E0202, so the rank is written in two
equations.

Group-by gets no combinator: an aggregate already groups by the variables it shares with the rule (`K`
above). Strings get no helpers either. The only string operation is `^`, so string helpers wait for
string primitives (Soufflé's `strlen`, `substr`), which is a separate issue.

### 5.6 `std/directives` and `std/demand`

`std/directives` collects what a directive author needs and what `%demand` already contains:
- the binding analysis `tvars` (today `tvarsOf`), `tsvars`, `fvars`, `fbound`, `fneeds`, `plain` and
  `plains`;
- `heads` and `body`, the parts of a `rule`;
- `rules : module -> list rule`;
- `calls : sym -> formula -> list (list term)`, the arguments of the calls of a relation, including under
  `not`, aggregates and disjunctions (today's `dcall` and `dinner` generalised);
- `reject : string -> list item`, which is `[ierror m]`;
- `fresh : string -> list string -> string`, a variable name that is not in the list, with `#` so that
  source syntax cannot capture it. This is the hygiene of `ot_demand_hygiene`.

`std/demand` is today's `demand` under
`%export { demand : (r : sym) -> modes (labels r) -> module -> module }.`, so its helpers are outside its
signature. It uses `if` and `std/list` in place of `band`, `bor`, `member`, `sdiff`, `shares`, `msym`,
`dkeepS`, `dunless` and `ditems`, and `std/directives` for the binding analysis. Rewriting it does not
change the rules it generates. The `--print-after stage` goldens of the `%demand` tests guard this.

## 6. Open questions, settled

### 6.1 Object `list` and meta `seq`

#80 settled this: `list A : data.` is one declaration at both stages, and `seq`, `snil` and `scons` are
gone. What remains is a duplication of *functions*. Meta `length` and object `len` cannot be one
definition, since #80 decided against stage-polymorphic functions. They stay two definitions in one
module, `std/list`, with the meta functions named after Lean's (`length`, `map`) and the object relations
after today's (`len`, `member`).

### 6.2 Built-in `%demand` for `len`

No. A module-wide directive rewrites its own file (reference: directives, footprints), and the seeds
belong to the call sites. The spike showed that the existing answer works across files:

```hugin,ignore
ls = %import "std/lists".
%demand ls.size +l -n.        (* size is len in the spike *)
?- ls.size [1, 2] N.          (* N = 2 *)
```

The demand rule in the program asserts the list (`size.check (cons 1 (cons 2 nil))`), and the imported
relation measures it. The reference already documents this for the prelude's `len` (reference:
directives, the note at the end of "Demand"), and only the module name changes. A list known at compile
time is measured by the meta `length`, with no demand.

### 6.3 An object `true` and an object `bool`

The reference Datalogs split into two questions:

| | boolean *value* type for columns | `true`/`false` as formulas |
|---|---|---|
| Soufflé | no (numbers with `land`, `lor`, `lnot`) | yes, nullary constraints |
| Flix | `Bool` | nullary predicates |
| CodeQL | `boolean` | `any()`, `none()` |
| Logica | literals | no |
| Rel | `Boolean` (`boolean_true`, `boolean_false`), "useful for importing data" | `true = {()}`, `false = {}` |

**Recommendation:**
- `bool : data.` in `std/reflect`, with `true` and `false` as shared constructors. Four of the five
  systems have a boolean value type, and Rel names the reason: data with boolean columns. With #80 this
  costs one word, since the meta `bool` and its use by `same` and `derived` do not change.
- No object formula `true` or `false`. A rule with an empty body is a fact. A rule whose body is false is
  not written. Generated code uses the empty body (`horn [h] []`), as `%demand` does.

A shared `bool` has one trap, and the spike shows it already exists for every nullary constant:
`q :- no.` with `no : flag` derives `q`, because a constant is a fact and a constant in a body is an
existence check. With `bool` shared, `p :- false.` would derive `p`. The recommendation therefore comes
with a lint, reported at the atom: "a nullary constant used as a formula always holds". The lint is on by
default and applies to every nullary constant, not only `bool`'s.

Rejected:
- Formula keywords `true`/`false`, which would clash with the constructors in object code.
- Keeping `bool` meta-only, which leaves boolean input columns to every program's own type.

## 7. Startup time

Method: the staged launcher of `9b82924`, on the 4-vCPU container of `docs/PERFORMANCE.md`. Another
agent's sbt build was running at the same time (load average 5 to 6), so every pair was measured
interleaved. *Trimmed* is today's prelude without `len`, `pair`, the graph section and the demand
section. It is close to the proposed `std/reflect` plus prelude, and includes `option` and all of
reflection.

| measurement | today | trimmed | change |
|---|---:|---:|---:|
| prelude elaboration, warm, uncached (31 runs after 30 warm-up, median; min in parentheses) | 47.4 ms (30.1) | 13.3 ms (8.5) | −72 % |
| prelude elaboration, warm, uncached (21 runs after 10 warm-up) | 80.4 ms | 19.1 ms | −76 % |
| first prelude elaboration in a new JVM (9 runs, median) | 2 155 ms | 1 374 ms | −36 % |
| cold `hugin check bench/small/one.hgn`, wall (9 runs, median) | 3 201 ms | 1 998 ms | −38 % |
| warm cached one-line compile (`StdlibCache`) | ~5 ms | ~5 ms | 0 |

- The warm figures come from a Java harness that calls `ProgramElab.prelude` on both texts in one JVM, as
  `Bench.elabPrelude` does.
- The cold figures use a copy of the staged launcher whose jar has the trimmed prelude.
- The cold absolute numbers are higher than in `docs/PERFORMANCE.md` because of the load. The ratios are
  the result.

A program that uses `%demand` pays the elaboration of `std/demand` once per process, which is about the
difference above. It pays nothing more than today. Rewriting the helpers on `std/list` (B4) must not make
`std/demand` slower than today's demand section. B4 measures this with the same harness.

## 8. Migration

**`--no-prelude`** loads nothing from `<stdlib>` unless the program imports it. A program compiled with
it can now `%import "std/reflect"`. `tests/pos/no_prelude` and `tests/neg/no_prelude` keep their output.
`tests/neg/e0917_no_prelude` keeps its error, and its note changes to "declared by `std/reflect`;
`--no-prelude` loads it only if imported".

**Programs** (`tests`, `examples`, `docs/design/examples`, `bench`):

| change | files |
|---|---|
| `%demand` | none (lazy re-export) |
| add `%use "std/graph".` (`tc`, `bounded`, `graph`) | `tests/run/{readme_example, ex_graphs, a10_meta_applicative, c2_primitive, lib/routes}`, `tests/repl/lib/routes`, `tests/neg/meta_types`, `tests/recovery/module_bodies`, `examples/graphs`, `docs/design/examples/graphs`, `bench/meta/meta_scaled` (and `BenchGen`, which writes it) |
| add `%use "std/list".` (`len`) | `tests/run/{t_termination_explain, imports, t_termination_len_callers, a06_termination_len, c2_primitive, ex_lists}`, `examples/lists`, `docs/design/examples/lists`, `bench/gen/large` |
| `band`, `bor` | `docs/design/examples/graphs`, `typechecker`: rewritten with `if` |
| `pair` | no program (the hits are the programs' own `pair`) |

The new line goes at the end of each file's leading comment. A neg or recovery golden whose diagnostics
come after it shifts by one line.

**Goldens that change:**

| golden | why |
|---|---|
| `run/t_termination_explain`, `run/t_termination_len_callers` | the termination explanation names `<stdlib>/std/list.hgn:N` for `<stdlib>/prelude.hgn:19` |
| `neg/e0923_shared_out_of_place` | "declared here" points into `std/reflect` (`list`) and the prelude (`option`) |
| `neg/e0917_no_prelude` | the note (above) |
| `neg/core_e0901_occurs` | the numbers of unknowns, as with every prelude change |
| `neg/meta_types`, `recovery/module_bodies` | one line shifted by the `%use` |
| `lsp/meta_completion`, `lsp/hover_staging` | the completion lists lose the moved names; hover on `len` names `std/list` |
| `neg/core_e0902_meta_as_object` | its note lists shareable types, and `bool` becomes one |

Output names do not change: object constants of `<stdlib>` files print without a prefix, as the prelude's
do today, unless the program declares the same name. `len[int]`, `cons` and functor instances print as
before. No `tests/run` answer changes.

**Scala tests** with embedded programs that use `tc`, `bounded`, `len` or `%demand`: `ModulesSuite`,
`FamiliesSuite`, `ImplicitsSuite`, `CompilerQueriesSuite`, `LibraryQueriesSuite`, `StagingHoverSuite`,
`LanguageServerSuite`, `SessionSuite`, `TerminationProblemsSuite`, `TransformSuite`, and the fuzz
`ProgramGen` (it generates `len` calls). `ReflectionSuite` keeps its bootstrap through the root-file
fallback (4.2). `StdlibCacheSuite` gains cases for `std/` files.

**Reference.**
- `prelude.md` is rewritten, `reflection.md` changes its "prelude" wording, and `directives.md` changes
  in its primitive directives, `%demand` and resolution sections.
- `modules.md` states the transparency of ascription as a rule, and gains `%export`, `%use`, `std/` paths
  and the scope picture.
- `docs/LIBRARIES.md` says E0101 for a hidden field; the implementation reports E0906, and the note is
  corrected.
- `introduction.md`, `modules.md` and `docs/errors/E0203.md`, `E0204.md` change their `tc` examples.
  `object/declarations.md` and `object/types.md` declare their own `pair`.
- New: a part "The standard library" with one page per module, and explanations for the new codes.

## 9. Batches

Each batch updates the reference, `docs/errors` and its goldens in the same PR. The sizes are changed
lines including tests and reference.

| batch | content | reference in the same PR | size |
|---|---|---|---|
| **B0** language | `%export S` (4.5), `%use` (open, selective, by the module's type; ambiguity E0109), `std/` import prefix; no library change | `modules.md` (signatures: transparency as a rule; imports: `%export`; `%use`; scopes), `directives.md` (directives opened by `%use`), `docs/errors/E0109.md`, `E0110.md`, the `%export` note of `E0204.md`, `E0906.md` on hidden fields | M: ~400 Scala, ~250 tests, ~200 reference |
| **B1** split | `std/reflect` with today's declarations plus `if`; the compiler looks up its names by file (4.2); the prelude becomes the `%use` lines and `option`; `std/graph` and `std/list` with today's `tc`, `bounded`, `len`; `std/demand` with today's code, re-exported eagerly; `pair` deleted; migration of section 8 | `prelude.md` rewritten; `reflection.md`, `directives.md`, `introduction.md`, `modules.md`; new part "The standard library" with pages for `std/reflect`, `std/graph`, `std/list`, `std/demand`; `E0203`, `E0204`, `E0917` | L: ~300 Scala, ~500 library, ~400 tests and goldens, ~500 reference |
| **B2** lazy | the lazy re-export of 4.8, with the check that the file declares no object constants; `StdlibCache` per `std/` file; numbers in `docs/PERFORMANCE.md` | `modules.md`: one paragraph on what `%use` in the prelude elaborates (a Note, since laziness is unobservable) | S: ~200 Scala, ~100 tests, ~20 reference |
| **B3** bool | `bool : data.`; the lint for nullary constants in bodies; `if` in the documented interface | `prelude.md`, `std/reflect` page, `object/rules.md` (constants as formulas), `docs/errors/W00xx.md` | S: ~150 Scala, ~150 tests, ~120 reference |
| **B4** lists and directives | `std/list` complete (5.3); `std/directives` (5.6); `std/demand` rewritten on both, helpers outside its `%export` signature; `docs/design/examples` rewritten with `std/list`; check that `std/demand` is not slower | `std/list` and `std/directives` pages, one `hugin,run` example per combinator; `std/demand` page | M: ~350 library, ~300 tests, ~350 reference |
| **B5** graphs and order | `std/graph` complete (5.4) and `std/order` (5.5); instance naming of composed functors | `std/graph` and `std/order` pages with run examples; `modules.md` on instance names | M: ~250 library, ~300 tests, ~350 reference |

Not scheduled: **B6 sealing**, the opaque ascription and manifest fields of 4.6, when a std module needs
an abstract type. It would carry `modules.md` ("Sealing"), a code for an operand on a sealed type, and an
update of `docs/LIBRARIES.md`; size M (~500 Scala, ~250 tests, ~200 reference).

B0 and B1 come first, in that order. B2, B3, B4 and B5 are independent of each other. B4 before B2 lets
the lazy check measure the rewritten `std/demand`. Every library definition passes coverage and
size-change termination, which the build checks. Every reference example is a `hugin,run` block.

## 10. Alternatives

**Keep everything in the prelude, and only fix shadowing.** The compiler already binds reflective names
by the prelude's scope, so a program's `term` is safe today. This was rejected because it fixes neither
the cost (section 7) nor the 144 names in every scope, which the issue asks to remove.

**A compiler-bound file that is not importable, with `std/reflect` as a re-exporting view.** This was
rejected because re-export through a module needs aliases, and an alias of a constructor is not a
constructor (it cannot be matched). One file that is both the compiler's and the user's import is
simpler.

**Idris-style registration pragmas** (`%builtin list` on the declaration) instead of lookup by name in a
fixed file. They make the binding visible in source. They were rejected because they are new syntax for a
list of about 60 names that changes once per redesign. The fixed file and `ReflectiveGlobals` already
express the list, in one place.

**`%demand` behind an explicit import** (`%use "std/demand".` in each program). This is simpler than lazy
re-export, and it is what the issue's "explicitly imported" suggests for everything else. It was rejected
because `%demand` is the language's tool for constructive recursion: the issue lists it with `%input` and
`%output` as a core directive. The cost argument is met by laziness without migrating 30 programs.

**SWI-style autoload of any `std` name on an unresolved reference.** This was rejected because the file
set of a compilation would depend on name resolution, and the import graph (`ImportGraph`), which the
query layer and the language server compute before elaboration, would no longer be static. 4.8 keeps the
graph static and only defers elaboration, for files whose evaluation is unobservable.

**Flix-style qualified access to every module without import.** This was rejected because Hugin names are
not hierarchical. `std.graph.tc` would need a global namespace, which Hugin does not have.

**A `private` modifier** (the first version of this note). It was rejected because it is a second hiding
mechanism beside signatures: it hides per declaration, not by an interface that can be named, read in one
place and ascribed again. Signatures already hide; only the file lacked a place to state one.

**Interface files** (`std/demand.hgni`, as OCaml's `.mli`). They were rejected because Hugin has no
separate compilation, which is what `.mli` files are for. A signature is a record type, an ordinary value
that a file can write and name, so an interface file would be a second syntax for it. It would also be a
second file to keep in step, with work in the loader, the query layer and the language server.

**`where`-local helpers** as the hiding mechanism. A spike moved a directive's helpers, quoted patterns
included, into the `where` block of its clause; they were hidden (`m.go` is E0906) and the directive ran.
This needs no addition, and `std/reflect` uses it for `pick`. It was rejected as the general mechanism:
it hides lexically inside one clause, has no forward references, cannot share helpers between two
exported functions, and does not state an interface.

**A sealed record inside the file** (`lib : S = { … }.`, 1ML's `List :> LIST = { … }`). It was rejected
because meta functions by clauses are E0907 in module bodies, and the file would still export `lib`.
Lifting E0907 is worth doing on its own, but it does not remove the need for `%export`.

**ML's stratified module language** (separate structures, signatures and functors). It was rejected
because Hugin already unifies them in dependent records, as 1ML does. Of the ML constructs, `where type`,
manifest specifications, `include`, sharing constraints, destructive substitution and `module type of`
are rejected or deferred, for the reasons in the table of 4.5.

**Directive paths `%m.d`** (the first version of this note). They were dropped, because `%use` opens a
module's directives, and a program can still define an alias (`symmetric = g.sym2.`).

**Closures as directives** (`%tc edge path.`). They work, but they duplicate the functors, and they
cannot compose. Functors are graph-to-graph functions, so `rtc (undirected g)` needs no new definition.

**`nat` merged with `index`.** One natural number type would serve fuel and de Bruijn indices. This was
rejected for now because it renames the constructors that reflection's data uses (`izero`, `isuc`), for
no gain in what programs can express.

## 11. Sources

The clones are shallow, made on 2026-10-09.

- Lean 4, `leanprover/lean4` at `0bb12a8`: `src/Init.lean`, `src/Init/Prelude.lean`,
  `src/Init/Core.lean`, `src/Init/Data/List/Basic.lean`, `src/Std.lean`, `src/Std/Data.lean`,
  `src/Lean/Elab/Import.lean`.
- Idris 2, `idris-lang/Idris2` at `1c630e6`: `libs/prelude/Prelude.idr`, `libs/prelude/Builtin.idr`,
  `libs/prelude/Prelude/Types.idr`, `libs/prelude/Prelude/Num.idr`, `libs/base/`.
- Agda standard library, `agda/agda-stdlib` at `2ffa8b7`: `src/Data/Nat.agda`, `src/Data/Nat/Base.agda`,
  `src/Data/List/Base.agda`, `src/Relation/Nullary/Decidable/Core.agda`,
  `src/Relation/Binary/Definitions.agda`, `src/Relation/Binary/Construct/Closure/`.
- GHC `base` Prelude: `libraries/base/src/Prelude.hs` from `ghc/ghc` `master`, fetched as a single file
  from raw.githubusercontent.com, since cloning GHC is out of proportion.
- relude, `kowainik/relude` at `5557fb2`: `src/Relude.hs`, `src/Relude/List/Reexport.hs`,
  `src/Relude/List/NonEmpty.hs`.
- Soufflé, `souffle-lang/souffle` at `f53dab8`: `src/parser/parser.yy`, `src/parser/scanner.ll`,
  `src/include/souffle/TypeAttribute.h`, `src/FunctorOps.cpp`, `tests/example/comp-parametrized/`.
- Flix, `flix/flix` at `534bfd8`: `main/src/library/Graph.flix`, `main/src/library/Prelude.flix`,
  `examples/datalog/`.
- CodeQL, `github/codeql` at `6efb2a1` (sparse): `shared/util/codeql/util/`,
  `shared/dataflow/codeql/dataflow/DataFlow.qll`, `docs/codeql/ql-language-reference/`.
- Logica, `EvgSkv/logica` at `8356e23`: `lib/`, `compiler/universe.py`, `compiler/dialect_libraries/`,
  `parser_py/parse.py`, `examples/scripts/closure_use.l`.
- Rel: its source is not public. The documentation pages rel.relational.ai/rel/ref/lib,
  rel.relational.ai/rel/ref/lib/stdlib and rel.relational.ai/rel/ref/data-types/other were read.
- 1ML, `rossberg/1ml` at `028859a`: `README.txt`, `prelude.1ml`; Rossberg, "1ML: Core and modules
  united", JFP 28 (2018), `people.mpi-sws.org/~rossberg/1ml/1ml-jfp.pdf`, read in full text.
- MixML: Rossberg and Dreyer, "Mixin' up the ML module system", TOPLAS 35(1) (2013),
  `people.mpi-sws.org/~rossberg/mixml/mixml-toplas.pdf`, read in full text.
- Agda: `agda-stdlib` as above, `src/Data/List/Sort.agda`, `src/Data/List/Sort/Base.agda`.
- SML: HaMLet, `rossberg/hamlet` at `37275b9`, `elab/ElabModule.sml`.
- OCaml, `ocaml/ocaml` at `6471927` (sparse): `stdlib/list.ml`, `stdlib/list.mli`, `stdlib/map.mli`,
  `manual/src/refman/compunit.etex`, `modtypes.etex`, `extensions/signaturesubstitution.etex`,
  `extensions/moduletypeof.etex`.
- SWI-Prolog, `SWI-Prolog/swipl-devel` at `6333852`: `library/lists.pl`, `library/apply.pl`,
  `library/aggregate.pl`, `boot/init.pl`.
- Hugin: `src/main/resources/hugin/stdlib/prelude.hgn`, `core/elab/Reflective.scala`,
  `core/elab/TypedQuotes.scala`, `core/elab/QuotedPatterns.scala`, `core/elab/Directives.scala`,
  `core/Primitives.scala`, `compiler/Libraries.scala`, `docs/NOTES.md` (C1, C2, C3, #80, #56),
  `docs/LIBRARIES.md`, `docs/PERFORMANCE.md`.
